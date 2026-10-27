module

public meta import Lean
public import Lean.Exception

namespace CFSG.KC.DecideFV

open Lean Meta Elab Tactic

elab "kc_decide_fv" : tactic => liftMetaFinishingTactic fun g => g.withContext do
  let t ← instantiateMVars (← g.getType)
  let t ← zetaReduce t
  if t.hasMVar then throwError "kc_decide_fv: the goal has metavariables{indentExpr t}"
  let inst ← synthInstance (mkApp (mkConst ``Decidable) t)
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let pf := mkApp3 (mkConst ``of_decide_eq_true) t inst refl
  let mut fvs : Array Expr := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      fvs := fvs.push d.toExpr
  let ty ← mkForallFVars fvs t
  let val ← mkLambdaFVars fvs pf
  let lvls := (collectLevelParams {} ty).params.toList
  let nm ← mkAuxLemma lvls ty val
  g.assign (mkAppN (mkConst nm (lvls.map mkLevelParam)) fvs)

end CFSG.KC.DecideFV
