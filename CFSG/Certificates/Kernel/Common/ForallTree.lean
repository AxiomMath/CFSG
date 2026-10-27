module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

public section

namespace CFSG.KC.ForallTree

theorem forall_lt_one {P : Nat → Prop} (h : P 0) : ∀ k < 1, P k := by
  intro k hk
  rw [Nat.lt_one_iff.1 hk]
  exact h

theorem forall_lt_add {P : Nat → Prop} {m n : Nat} (h1 : ∀ k < m, P k)
    (h2 : ∀ k < n, P (m + k)) : ∀ k < m + n, P k := by
  intro k hk
  by_cases h : k < m
  · exact h1 k h
  · have := h2 (k - m) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this

end CFSG.KC.ForallTree

open Lean Elab Command Meta

meta partial def CFSG.KC.ForallTree.build (base : Name) (Q : Expr) (off len : Nat) : Expr :=
  if len ≤ 1 then
    mkApp2 (mkConst ``CFSG.KC.ForallTree.forall_lt_one) Q (mkConst (base.appendAfter s!"{off}"))
  else
    let m := len / 2
    let natE := mkConst ``Nat
    let addE := mkAppN (mkConst ``HAdd.hAdd [0, 0, 0])
      #[natE, natE, natE, mkApp2 (mkConst ``instHAdd [0]) natE (mkConst ``instAddNat)]
    let Q2 := mkLambda `k .default natE (mkApp Q (mkApp2 addE (mkRawNatLit m) (.bvar 0)))
    mkAppN (mkConst ``CFSG.KC.ForallTree.forall_lt_add)
      #[Q, mkRawNatLit m, mkRawNatLit (len - m), build base Q off m, build base Q2 (off + m) (len - m)]

elab "#kc_forall_tree " nm:ident p:term:max n:num pre:ident : command => do
  let natT := mkConst ``Nat
  liftTermElabM do
    let P ← Term.elabTerm p (some (mkForall `k .default natT (mkSort .zero)))
    Term.synthesizeSyntheticMVarsNoPostponing
    let P ← instantiateMVars P
    if P.hasMVar || P.hasFVar then throwError "#kc_forall_tree: the predicate is not closed"
    let n := n.getNat
    if n = 0 then throwError "#kc_forall_tree: n = 0"
    let base := pre.getId
    let env ← getEnv
    for k in [0:n] do
      let t := base.appendAfter s!"{k}"
      unless env.contains t do throwError "#kc_forall_tree: unknown theorem {t}"
    let pf := CFSG.KC.ForallTree.build base P 0 n
    let ltE := mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, .bvar 0, mkRawNatLit n]
    let ty := mkForall `k .default natT (mkForall `h .default ltE (mkApp P (.bvar 1)).headBeta)
    let name := (← getCurrNamespace) ++ nm.getId
    withOptions (Elab.async.set · false) <|
      CFSG.KC.addThmDecl <| { name, levelParams := [], type := ty, value := pf }
