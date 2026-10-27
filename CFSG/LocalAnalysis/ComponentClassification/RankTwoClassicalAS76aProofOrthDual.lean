module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {ι K : Type} [Field K] (Q : QuadraticForm K (ι → K))

theorem quad_add (x y : ι → K) : Q (x + y) = Q x + Q y + Q.polarBilin x y := by
  rw [polarBilin_apply_apply]
  exact map_add_eq Q x y

theorem polarBilin_comm (x y : ι → K) : Q.polarBilin x y = Q.polarBilin y x := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_comm]

theorem apply_sum_smul_eq_zero {k : ℕ} (w : Fin k → ι → K) (hQ : ∀ i, Q (w i) = 0)
    (hB : ∀ i j, Q.polarBilin (w i) (w j) = 0) (c : Fin k → K) :
    Q (∑ i, c i • w i) = 0 := by
  classical
  have key : ∀ s : Finset (Fin k), Q (∑ i ∈ s, c i • w i) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, quad_add, ih, QuadraticMap.map_smul, hQ, smul_zero, zero_add,
        zero_add, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, map_smul, LinearMap.smul_apply, hB, smul_zero, smul_zero]
  exact key Finset.univ

theorem exists_polar_dual [Fintype ι] (hQ : Q.polarBilin.Nondegenerate) {ρ : Type} [Fintype ρ]
    [DecidableEq ρ] (g : ρ → ι → K) (hg : LinearIndependent K g) :
    ∃ w : ρ → ι → K, ∀ r s, Q.polarBilin (g r) (w s) = if r = s then 1 else 0 := by
  let bW := Basis.span hg
  choose φ hφ using fun s => LinearMap.exists_extend (bW.coord s)
  refine ⟨fun s => (LinearMap.BilinForm.toDual Q.polarBilin hQ).symm (φ s), fun r s => ?_⟩
  rw [polarBilin_comm, ← LinearMap.BilinForm.toDual_def hQ, LinearEquiv.apply_symm_apply]
  have h := congrArg (fun f : ↥(Submodule.span K (Set.range g)) →ₗ[K] K => f (bW r)) (hφ s)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Basis.coord_apply,
    Basis.repr_self, Finsupp.single_apply] at h
  rw [show ((bW r : ↥(Submodule.span K (Set.range g))) : ι → K) = g r from
    congrArg Subtype.val (Basis.span_apply hg r)] at h
  rw [h]

variable [CharP K 2]

theorem exists_singular_dual {k : ℕ} (u u' : Fin k → ι → K) (hQu : ∀ i, Q (u i) = 0)
    (huu : ∀ i j, Q.polarBilin (u i) (u j) = 0)
    (hdual : ∀ i j, Q.polarBilin (u i) (u' j) = if i = j then 1 else 0) :
    ∃ u'' : Fin k → ι → K, (∀ i j, Q.polarBilin (u i) (u'' j) = if i = j then 1 else 0) ∧
      (∀ i j, Q.polarBilin (u'' i) (u'' j) = 0) ∧ (∀ j, Q (u'' j) = 0) ∧
      ∀ j, ∃ c : Fin k → K, u'' j = u' j + ∑ m, c m • u m := by
  classical
  set G : Fin k → Fin k → K := fun i j => Q.polarBilin (u' i) (u' j) with hG
  let c : Fin k → Fin k → K := fun j i => if i < j then G i j else if i = j then Q (u' i) else 0
  have hu'u : ∀ i m, Q.polarBilin (u' i) (u m) = if m = i then 1 else 0 := fun i m => by
    rw [polarBilin_comm, hdual]
  refine ⟨fun j => u' j + ∑ m, c j m • u m, fun i j => ?_, fun i j => ?_, fun j => ?_,
    fun j => ⟨c j, rfl⟩⟩
  · rw [map_add, map_sum, hdual]
    simp [huu]
  · dsimp only
    simp only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul, hu'u, hdual, huu, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero, add_zero]
    change G i j + c i j + c j i = 0
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp only [c, hij, not_lt.mpr hij.le, ne_of_gt hij, ↓reduceIte, add_zero,
        CharTwo.add_self_eq_zero]
    · simp only [c, lt_irrefl, ↓reduceIte]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      show Q.polarBilin (u' i) (u' i) = 0
      rw [polarBilin_apply_apply]
      exact polar_self_eq_zero Q (u' i)
    · simp only [c, hij, not_lt.mpr hij.le, ne_of_gt hij, ↓reduceIte, add_zero]
      show Q.polarBilin (u' i) (u' j) + Q.polarBilin (u' j) (u' i) = 0
      rw [polarBilin_comm Q (u' j), CharTwo.add_self_eq_zero]
  · dsimp only
    rw [quad_add, apply_sum_smul_eq_zero Q u hQu huu, add_zero, map_sum]
    simp only [map_smul, smul_eq_mul, hu'u, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    simp only [c, lt_irrefl, ↓reduceIte, CharTwo.add_self_eq_zero]

end CFSG.ComponentClassification.RankTwoClassical
