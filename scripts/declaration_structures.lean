import Mathlib.Lean.CoreM
import Mathlib.Lean.Expr.Basic
import Batteries.Lean.HashMap

open Lean Meta

/-- Data about a single binder in a type -/
structure BinderData where
  kind : String  -- "forall", "lambda", "arrow"
  name : String
  type : String
  implicit : Bool
  instImplicit : Bool  -- typeclass
  level : Nat  -- nesting depth
  deriving Repr

/-- Complete structural analysis of a declaration -/
structure DeclStructure where
  name : String
  kind : String
  type : String
  binders : Array BinderData
  num_explicit_premises : Nat
  num_implicit_args : Nat
  num_typeclass_constraints : Nat
  num_forall : Nat
  num_exists : Nat
  num_arrows : Nat  -- non-dependent arrows (premises)
  max_nesting_depth : Nat
  conclusion_head : String
  conclusion_arity : Nat
  uses_classical : Bool
  namespace_depth : Nat
  is_polymorphic : Bool  -- has universe parameters
  has_decidable_instances : Bool
  deriving Repr

/-- Safely convert expression to string, with fallback -/
def safeExprToString (e : Expr) : MetaM String := do
  try
    let pp ← ppExpr e
    return toString pp
  catch _ =>
    -- Fallback: just return a placeholder
    return s!"<expr:{e.hash}>"

/-- Recursively collect all binders from an expression -/
partial def collectBinders (e : Expr) (depth : Nat := 0) : 
    MetaM (Array BinderData × Expr) := do
  -- Limit depth to prevent infinite recursion/timeout
  if depth > 50 then
    return (#[], e)
  try
    match e with
    | Expr.forallE name type body bi =>
      -- Safer type string extraction
      let typeStr ← try
        safeExprToString type
      catch _ =>
        pure "<type>"
      
      -- Check if this is an arrow (non-dependent function type)
      -- Just check the body directly without instantiation
      let isArrow := !body.hasLooseBVar 0
      let kind := if isArrow then "arrow" else "forall"
      let binder : BinderData := {
        kind := kind
        name := name.toString
        type := typeStr
        implicit := bi.isImplicit
        instImplicit := bi.isInstImplicit
        level := depth
      }
      
      -- For recursive call, we need to be careful with bound variables
      -- Create a fresh free variable to substitute
      let fvarId ← mkFreshFVarId
      let fvar := Expr.fvar fvarId
      let bodySubst := body.instantiate1 fvar
      
      -- Recursively process the substituted body
      let (restBinders, conclusion) ← collectBinders bodySubst (depth + 1)
      return (#[binder] ++ restBinders, conclusion)
    | Expr.lam name type body bi =>
      let typeStr ← try
        safeExprToString type
      catch _ =>
        pure "<type>"
      
      let binder : BinderData := {
        kind := "lambda"
        name := name.toString
        type := typeStr
        implicit := bi.isImplicit
        instImplicit := bi.isInstImplicit
        level := depth
      }
      
      -- Create a fresh free variable to substitute
      let fvarId ← mkFreshFVarId
      let fvar := Expr.fvar fvarId
      let bodySubst := body.instantiate1 fvar
      
      -- Recursively process the substituted body
      let (restBinders, conclusion) ← collectBinders bodySubst (depth + 1)
      return (#[binder] ++ restBinders, conclusion)
    | _ => return (#[], e)
  catch _ =>
    -- If anything fails, just return what we have
    return (#[], e)

/-- Get the head symbol of an expression -/
def getHeadSymbol (e : Expr) : MetaM String := do
  let e := e.getAppFn
  match e with
  | Expr.const name _ => return name.toString
  | Expr.fvar id => return id.name.toString
  | _ => return e.ctorName

/-- Check if expression uses classical logic -/
def usesClassicalLogic (e : Expr) : Bool :=
  e.find? (fun sub => 
    sub.isConstOf ``Classical.choice || 
    sub.isConstOf ``Classical.em ||
    sub.isConstOf ``Classical.propDecidable
  ) |>.isSome

/-- Check if expression has decidable instances -/
def hasDecidableInstances (e : Expr) : Bool :=
  e.find? (fun sub =>
    sub.isAppOfArity ``Decidable 1 ||
    sub.isAppOfArity ``DecidableEq 1
  ) |>.isSome

/-- Count existential quantifiers in an expression -/
partial def countExists (e : Expr) : Nat :=
  match e with
  | Expr.app (Expr.const ``Exists _) _ => 1 + countExistsInChildren e
  | _ => countExistsInChildren e
where
  countExistsInChildren (e : Expr) : Nat :=
    match e with
    | Expr.app f a => countExists f + countExists a
    | Expr.lam _ t b _ => countExists t + countExists b
    | Expr.forallE _ t b _ => countExists t + countExists b
    | Expr.letE _ t v b _ => countExists t + countExists v + countExists b
    | Expr.mdata _ e => countExists e
    | Expr.proj _ _ e => countExists e
    | _ => 0

/-- Analyze a declaration's type structure -/
def analyzeExpr (name : Name) (e : Expr) : MetaM DeclStructure := do
  -- Increase heartbeat limit for complex expressions
  withOptions (fun o => o.set `maxHeartbeats (1000000 : Nat)) do
    let (binders, conclusion) ← collectBinders e
    
    let explicitPremises := binders.filter fun b => 
      b.kind == "arrow" && !b.implicit && !b.instImplicit
    
    let implicitArgs := binders.filter fun b =>
      b.implicit && !b.instImplicit && b.kind != "arrow"
      
    let typeclassConstraints := binders.filter fun b =>
      b.instImplicit
    
    let forallCount := binders.filter (·.kind == "forall") |>.size
    let arrowCount := binders.filter (·.kind == "arrow") |>.size
    let existsCount := countExists conclusion
    
    let maxDepth := binders.map (·.level) |>.foldl max 0
    
    let conclusionHead ← getHeadSymbol conclusion
    let conclusionArity := conclusion.getAppNumArgs
    
    let usesClassical := usesClassicalLogic e
    let hasDecidable := hasDecidableInstances e
    
    let namespaceDepth := name.components.length
    let isPolymorphic := e.hasLevelParam
    
    let typeStr ← safeExprToString e  -- Use safe version
    
    return {
      name := name.toString
      kind := ""  -- will be set by caller
      type := typeStr
      binders := binders
      num_explicit_premises := explicitPremises.size
      num_implicit_args := implicitArgs.size
      num_typeclass_constraints := typeclassConstraints.size
      num_forall := forallCount
      num_exists := existsCount
      num_arrows := arrowCount
      max_nesting_depth := maxDepth
      conclusion_head := conclusionHead
      conclusion_arity := conclusionArity
      uses_classical := usesClassical
      namespace_depth := namespaceDepth
      is_polymorphic := isPolymorphic
      has_decidable_instances := hasDecidable
    }

/-- Convert structure to JSON format -/
def DeclStructure.toJson (s : DeclStructure) : String :=
  -- Manual JSON construction to avoid missing ToJson instances
  let bindersJson := s.binders.map fun b =>
    s!"\{\"kind\":\"{b.kind}\",\"name\":\"{b.name.replace "\"" "\\\"" |>.replace "\\" "\\\\"}\",\"type\":\"{b.type.replace "\"" "\\\"" |>.replace "\n" "\\n" |>.replace "\\" "\\\\"}\",\"implicit\":{b.implicit},\"instImplicit\":{b.instImplicit},\"level\":{b.level}}"
  let bindersStr := "[" ++ ",".intercalate bindersJson.toList ++ "]"
  
  s!"\{\"name\":\"{s.name.replace "\"" "\\\"" |>.replace "\\" "\\\\"}\",\"kind\":\"{s.kind}\",\"type\":\"{s.type.replace "\"" "\\\"" |>.replace "\n" "\\n" |>.replace "\\" "\\\\"}\",\"binders\":{bindersStr},\"num_explicit_premises\":{s.num_explicit_premises},\"num_implicit_args\":{s.num_implicit_args},\"num_typeclass_constraints\":{s.num_typeclass_constraints},\"num_forall\":{s.num_forall},\"num_exists\":{s.num_exists},\"num_arrows\":{s.num_arrows},\"max_nesting_depth\":{s.max_nesting_depth},\"conclusion_head\":\"{s.conclusion_head.replace "\"" "\\\"" |>.replace "\\" "\\\\"}\",\"conclusion_arity\":{s.conclusion_arity},\"uses_classical\":{s.uses_classical},\"namespace_depth\":{s.namespace_depth},\"is_polymorphic\":{s.is_polymorphic},\"has_decidable_instances\":{s.has_decidable_instances}}"

def Lean.ConstantInfo.kind : ConstantInfo → String
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "def"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"

-- Statistics tracking
structure Stats where
  total : Nat := 0
  processed : Nat := 0
  failed : Nat := 0
  skipped : Nat := 0
  deriving Repr

def main (args : List String) : IO UInt32 := do
  unsafe enableInitializersExecution
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  initSearchPath (← findSysroot)
  
  let stats : IO.Ref Stats ← IO.mkRef {}
  
  CoreM.withImportModules modules do
    let env ← getEnv
    let constants := env.constants.map₁.toList
    
    IO.eprintln s!"Total constants in environment: {constants.length}"
    
    for (n, c) in constants do
      stats.modify fun s => { s with total := s.total + 1 }
      
      if ! (← n.isBlackListed) then
        -- Skip internal/auxiliary definitions
        if !n.isInternal && !n.isImplementationDetail then
          try
            -- Check for extremely large types that might timeout
            if c.type.approxDepth > 100 then
              stats.modify fun s => { s with skipped := s.skipped + 1 }
            else
              -- Run with increased heartbeat limit globally
              let declStruct ← MetaM.run' do
                withOptions (fun o => o.set `maxHeartbeats (5000000 : Nat)) do
                  analyzeExpr n c.type
              let declStructWithKind := { declStruct with kind := c.kind }
              IO.println declStructWithKind.toJson
              stats.modify fun s => { s with processed := s.processed + 1 }
            
            -- Progress reporting every 10000 declarations
            let s ← stats.get
            if s.processed % 10000 == 0 then
              IO.eprintln s!"Processed {s.processed} declarations..."
          catch _ =>
            stats.modify fun s => { s with failed := s.failed + 1 }
            -- Log the error for debugging - only first 10
            let s ← stats.get
            if s.failed <= 10 then
              IO.eprintln s!"Failed to analyze {n}"
        else
          stats.modify fun s => { s with skipped := s.skipped + 1 }
      else
        stats.modify fun s => { s with skipped := s.skipped + 1 }
    
    -- Print final statistics
    let finalStats ← stats.get
    IO.eprintln "=== Extraction Statistics ==="
    IO.eprintln s!"Total declarations: {finalStats.total}"
    IO.eprintln s!"Successfully processed: {finalStats.processed}"
    IO.eprintln s!"Failed to process: {finalStats.failed}"
    IO.eprintln s!"Skipped (internal/blacklisted): {finalStats.skipped}"
    
  return 0