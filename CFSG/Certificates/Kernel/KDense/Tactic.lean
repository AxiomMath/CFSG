module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.Lce
public import Lean.Exception

public section

namespace CFSG.KC.KDense

theorem allLt_zero {P : Nat → Prop} : ∀ k < 0, P k := fun _ h => absurd h (Nat.not_lt_zero _)

theorem allLt_succ {P : Nat → Prop} {n : Nat} (h : ∀ k < n, P k) (hn : P n) : ∀ k < n + 1, P k :=
  fun k hk => (Nat.lt_succ_iff_lt_or_eq.1 hk).elim (h k) (fun e => e ▸ hn)

open Lean Meta Elab Tactic in
elab "kd_all " pre:ident n:num : tactic => liftMetaFinishingTactic fun g => do
  let ty ← instantiateMVars (← g.getType)
  let .forallE kn kt (.forallE _ _ body _) _ := ty
    | throwError "kd_all: the goal is not of the form ∀ k < n, P k"
  let P := Expr.lam kn kt (body.lowerLooseBVars 1 1) .default
  let mut prf := mkApp (mkConst ``allLt_zero) P
  for k in [0:n.getNat] do
    let tk := mkConst (pre.getId ++ Name.mkSimple s!"t{k}")
    prf := mkAppN (mkConst ``allLt_succ) #[P, mkRawNatLit k, prf, tk]
  g.assign prf

theorem andB_true {a b : Bool} (ha : a = true) (hb : b = true) : CFSG.KC.andB a b = true := by
  subst ha; exact hb

open Lean Meta Elab Tactic in
elab "kd_andB " ts:ident* : tactic => liftMetaFinishingTactic fun g => do
  let mut prf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let mut b := mkConst ``Bool.true
  for t in ts.reverse do
    let c := mkConst (← realizeGlobalConstNoOverload t)
    let ty ← inferType c
    let some (_, a, _) := ty.eq? | throwError "kd_andB: {t} is not an equation"
    prf := mkAppN (mkConst ``andB_true) #[a, b, c, prf]
    b := mkApp2 (mkConst ``CFSG.KC.andB) a b
  g.assign prf

end CFSG.KC.KDense

end
