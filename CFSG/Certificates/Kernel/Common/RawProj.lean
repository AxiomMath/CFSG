module

public meta import Lean

open Lean Elab Term Meta

elab "rawProj% " t:term : term <= ty => do
  let t ← instantiateMVars (← elabTermEnsuringType t ty)
  let .const fn _ := t.getAppFn |
    throwError "rawProj%: expected a projection application, got{indentExpr t}"
  let some info ← getProjectionFnInfo? fn |
    throwError "rawProj%: {fn} is not a projection function"
  if info.fromClass then throwError "rawProj%: {fn} is a class projection"
  unless t.getAppNumArgs == info.numParams + 1 do
    throwError "rawProj%: {fn} is not applied to exactly its parameters and the structure"
  let some (.ctorInfo c) := (← getEnv).find? info.ctorName | throwError "rawProj%: no constructor"
  return .proj c.induct info.i t.appArg!
