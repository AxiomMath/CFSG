module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSimpleDefs
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

@[expose] def PGen.holdsBase {G : Type*} [Group G] (a b : G) (c : PGen) : Prop :=
  evalPW a b c.z ^ c.p = 1 ∧ evalPW a b c.z ≠ 1 ∧
  (∀ w ∈ c.ts, evalPW a b w * evalPW a b w = 1 ∧ evalPW a b w ≠ 1 ∧
      evalPW a b c.z * evalPW a b w = evalPW a b w * evalPW a b c.z) ∧
  (∀ n ∈ c.ns, evalPW a b n.1 * evalPW a b c.z * (evalPW a b n.1)⁻¹ = evalPW a b c.z ^ n.2.1 ∧
      evalPW a b n.1 * evalPW a b c.z ^ n.2.2 * (evalPW a b n.1)⁻¹ = evalPW a b c.z) ∧
  (∀ m ∈ c.ms, ∃ w ∈ c.ts, evalPW a b m.1 * evalPW a b w = evalPW a b w * evalPW a b m.1)

@[expose] def PGen.checkBase {G : Type*} [Group G] [DecidableEq G] (a b : G) (c : PGen) : Bool :=
  let z := evalPW a b c.z
  decide (z ^ c.p = 1) && decide (z ≠ 1) &&
  c.ts.all (fun w =>
    let t := evalPW a b w
    decide (t * t = 1) && decide (t ≠ 1) && decide (z * t = t * z)) &&
  c.ns.all (fun n =>
    let x := evalPW a b n.1
    decide (x * z * x⁻¹ = z ^ n.2.1) && decide (x * z ^ n.2.2 * x⁻¹ = z)) &&
  c.ms.all (fun m =>
    let x := evalPW a b m.1
    c.ts.any (fun w => let t := evalPW a b w; decide (x * t = t * x)))

structure PSec where
  base : PGen
  h1 : List (ℕ × ℕ)
  h2 : List (ℕ × ℕ)
  simple : PSimple

@[expose] def PSec.check {G : Type*} [Group G] [DecidableEq G] (cn : G → G) (a b : G) (c : PSec) :
    Bool :=
  c.base.checkBase a b &&
  c.simple.check (cn (evalIdx (c.base.regs a b) c.h1)) (cn (evalIdx (c.base.regs a b) c.h2))
    (cn (evalPW a b c.base.z))

theorem getD_ofFn_fin {n : ℕ} (σ : Fin n → Fin n) (i : Fin n) : (List.ofFn σ).getD i.1 i = σ i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

@[expose] def canonPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  let tbl := List.ofFn σ
  let tinv := List.ofFn σ.symm
  have h1 : ∀ i : Fin n, tbl.getD i.1 i = σ i := fun i => getD_ofFn_fin σ i
  have h2 : ∀ i : Fin n, tinv.getD i.1 i = σ.symm i := fun i => getD_ofFn_fin σ.symm i
  { toFun := fun i => tbl.getD i.1 i
    invFun := fun i => tinv.getD i.1 i
    left_inv := fun i => by
      show tinv.getD (tbl.getD i.1 i).1 (tbl.getD i.1 i) = i
      rw [h1 i, h2 (σ i)]
      exact σ.symm_apply_apply i
    right_inv := fun i => by
      show tbl.getD (tinv.getD i.1 i).1 (tinv.getD i.1 i) = i
      rw [h2 i, h1 (σ.symm i)]
      exact σ.apply_symm_apply i }

theorem canonPerm_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) : canonPerm σ = σ :=
  Equiv.ext fun i => getD_ofFn_fin σ i

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
