module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismLinearKernel

public section

namespace CFSG.ProperTwoGeneratedCore.BenderFacts

open CFSG.BenderSuzuki.MatrixGroups

theorem exists_mem_eq_conj_of_fixes_sylow_of_mulEquiv_psl2 {K : Type*} [Field K] [Finite K]
    {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f) {J : Type*} [Group J]
    (e : J ≃* PSL2MatrixGroup K) (R : Sylow 2 J) (α : MulAut J)
    (hα : ∀ r ∈ (R : Subgroup J), α r = r) : ∃ j ∈ (R : Subgroup J), α = MulAut.conj j := by
  refine RootCenter.linear_rank_one_Sylow_layer_kernel_of_mulEquiv hf hcard e R _ rfl α ?_ ?_ ?_
  · ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      change α r ∈ (R : Subgroup J)
      rw [hα r hr]
      exact hr
    · intro hx
      exact ⟨x, hx, hα x hx⟩
  · rintro _ ⟨v, -, rfl⟩
    exact hα v v.2
  · intro x hx
    rw [hα x hx, inv_mul_cancel]
    exact one_mem _

theorem exists_mem_eq_conj_of_fixes_sylow_of_mulEquiv_psl2Binary {m : ℕ} (hm : 2 ≤ m)
    {J : Type*} [Group J] (e : J ≃* PSL2BinaryMatrixGroup m) (R : Sylow 2 J) (α : MulAut J)
    (hα : ∀ r ∈ (R : Subgroup J), α r = r) : ∃ j ∈ (R : Subgroup J), α = MulAut.conj j := by
  have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have : Finite (GaloisField 2 m) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  exact exists_mem_eq_conj_of_fixes_sylow_of_mulEquiv_psl2 hm hcard e R α hα

end CFSG.ProperTwoGeneratedCore.BenderFacts
