module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3Mat

public noncomputable section

namespace CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3

section Normalizer

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem lower_entries_zero {M : Matrix (HypIndex 1 1) (HypIndex 1 1) K} {x₀ x' : UHeis h}
    (hx₀a : x₀.a = 0) (hx'a : x'.a = 0) (hc₀ : x₀.c ≠ 0) (hc' : x'.c ≠ 0)
    (heq : M * uMat x₀ = uMat x' * M) :
    M (.inr (.inl 0)) (.inl 0) = 0 ∧ M (.inr (.inr 0)) (.inl 0) = 0 ∧
      M (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
  have e1 := congrFun (congrFun heq (.inr (.inl 0))) (.inr (.inr 0))
  have e2 := congrFun (congrFun heq (.inr (.inr 0))) (.inr (.inr 0))
  have e3 := congrFun (congrFun heq (.inl 0)) (.inr (.inl 0))
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
    Fin.default_eq_zero, uMat_ee, uMat_ez, uMat_ef, uMat_ze, uMat_zz, uMat_zf, uMat_fe, uMat_fz,
    uMat_ff, hx₀a, hx'a, map_zero, neg_zero] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩
  · have : M (.inr (.inl 0)) (.inl 0) * x₀.c = 0 := by linear_combination e1
    exact (mul_eq_zero.mp this).resolve_right hc₀
  · have : M (.inr (.inr 0)) (.inl 0) * x₀.c = 0 := by linear_combination e2
    exact (mul_eq_zero.mp this).resolve_right hc₀
  · have : x'.c * M (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by linear_combination -e3
    exact (mul_eq_zero.mp this).resolve_left hc'

theorem pCoreOf_eq_of_sylow {P : Type} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (S : Sylow p P) {U N : Subgroup P} (hS : (S : Subgroup P) = U) (hUN : U ≤ N)
    (hle : N ≤ Subgroup.normalizer (U : Set P)) : CFSG.Open.pCoreOf p N = U := by
  have hUp : IsPGroup p U := by
    rw [← hS]
    exact S.isPGroup'
  apply le_antisymm
  · have hQ : IsPGroup p (CFSG.Open.pCoreOf p N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup p N
    have hQN := CFSG.LieType.BorelTits.pCoreOf_le p N
    have hSset : (S : Set P) = (U : Set P) :=
      congrArg (fun T : Subgroup P => (T : Set P)) hS
    have hQnorm : CFSG.Open.pCoreOf p N ≤ Subgroup.normalizer (S : Set P) := by
      rw [hSset]
      exact hQN.trans hle
    have := hQ.inf_normalizer_sylow S
    rw [inf_eq_left.mpr hQnorm] at this
    exact this.le.trans (inf_le_right.trans hS.le)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hUN hle hUp

end Normalizer

end CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3
