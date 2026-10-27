module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLSplit

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.BurgD

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.Burgoyne.PSL

variable {K : Type} [Field K]

theorem trace_signMat {n : ℕ} (J : Finset (Fin n)) :
    (signMat K J).trace = (Jᶜ.card : K) - J.card := by
  rw [signMat, trace_diagonal, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_not, Finset.filter_mem_eq_inter,
    Finset.univ_inter, ← Finset.compl_eq_univ_sdiff, nsmul_eq_mul, nsmul_eq_mul, mul_neg,
    mul_one, mul_one]
  ring

theorem trace_signMat_ne_zero (h2 : (2 : K) ≠ 0) {J : Finset (Fin 4)} (hJ : Odd J.card) :
    (signMat K J).trace ≠ 0 := by
  rw [trace_signMat]
  have hc : Jᶜ.card = 4 - J.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hle : J.card ≤ 4 := by simpa using J.card_le_univ
  obtain ⟨m, hm⟩ := hJ
  rcases (show J.card = 1 ∨ J.card = 3 by omega) with h | h
  · rw [hc, h]
    norm_num
    exact h2
  · rw [hc, h]
    norm_num
    exact h2

theorem eq_one_of_conj_signMat (h2 : (2 : K) ≠ 0) {J : Finset (Fin 4)} (hJ : Odd J.card)
    (B : GL (Fin 4) K) {c : K}
    (h : (B : Matrix (Fin 4) (Fin 4) K) * signMat K J *
      ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = c • signMat K J) : c = 1 := by
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul, Matrix.trace_smul, smul_eq_mul] at ht
  have hne := trace_signMat_ne_zero h2 hJ (K := K)
  have h0 : (1 - c) * (signMat K J).trace = 0 := by linear_combination ht
  rcases mul_eq_zero.1 h0 with h1 | h1
  · linear_combination -h1
  · exact absurd h1 hne

theorem signGL_inv (J : Finset (Fin 4)) : (signGL K J)⁻¹ = signGL K J :=
  inv_eq_of_mul_eq_one_right (Units.ext (signMat_mul_self J))

theorem commute_of_conjAut_conj [Finite K] (h2 : (2 : K) ≠ 0) {J : Finset (Fin 4)}
    (hJ : Odd J.card) (B : GL (Fin 4) K)
    (h : conjAut 4 K (B * signGL K J * B⁻¹) = conjAut 4 K (signGL K J)) :
    (B : Matrix (Fin 4) (Fin 4) K) * signMat K J = signMat K J * B := by
  have h1 : conjAut 4 K (B * signGL K J * B⁻¹ * (signGL K J)⁻¹) * fieldAut 4 K 1 = 1 := by
    rw [map_one, mul_one, map_mul, h, map_inv, mul_inv_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ 1 h1
  have h3 : B * signGL K J * B⁻¹ = GeneralLinearGroup.scalar (Fin 4) c * signGL K J := by
    rw [hc, inv_mul_cancel_right]
  have h4 : (B : Matrix (Fin 4) (Fin 4) K) * signMat K J *
      ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (c : K) • signMat K J := by
    have := congrArg (fun M : GL (Fin 4) K => (M : Matrix (Fin 4) (Fin 4) K)) h3
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_signGL] at this
    rw [this, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hc1 := eq_one_of_conj_signMat h2 hJ B h4
  rw [hc1, one_smul] at h4
  calc (B : Matrix (Fin 4) (Fin 4) K) * signMat K J
      = (B : Matrix (Fin 4) (Fin 4) K) * signMat K J *
          (((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * B) := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    _ = signMat K J * B := by rw [← Matrix.mul_assoc, h4]

theorem exists_singleton_block {J : Finset (Fin 4)} (hJ : Odd J.card) :
    ∃ k : Fin 4, ∀ i, i ≠ k → (i ∈ J ↔ k ∉ J) := by
  have hle : J.card ≤ 4 := by simpa using J.card_le_univ
  obtain ⟨m, hm⟩ := hJ
  rcases (show J.card = 1 ∨ J.card = 3 by omega) with h | h
  · obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 h
    exact ⟨k, fun i hi => by simp [hi]⟩
  · have hc : Jᶜ.card = 1 := by rw [Finset.card_compl, Fintype.card_fin, h]
    obtain ⟨k, hk⟩ := Finset.card_eq_one.1 hc
    refine ⟨k, fun i hi => ?_⟩
    have hkJ : k ∉ J := by
      rw [← Finset.mem_compl, hk]
      exact Finset.mem_singleton_self k
    have hiJ : i ∈ J := by
      by_contra hiJ
      rw [← Finset.mem_compl, hk, Finset.mem_singleton] at hiJ
      exact hi hiJ
    exact iff_of_true hiJ hkJ

theorem apply_eq_zero_of_commute (h2 : (2 : K) ≠ 0) {J : Finset (Fin 4)} {k : Fin 4}
    (hk : ∀ i, i ≠ k → (i ∈ J ↔ k ∉ J)) {M : Matrix (Fin 4) (Fin 4) K}
    (hM : M * signMat K J = signMat K J * M) {i : Fin 4} (hi : i ≠ k) :
    M i k = 0 ∧ M k i = 0 := by
  have hc := (commute_compInd_iff J M).1 ((commute_signMat_iff h2 J M).1 hM.symm)
  have hik := hk i hi
  exact ⟨hc i k hik, hc k i (by tauto)⟩

theorem mul_self_apply_singleton (h2 : (2 : K) ≠ 0) {J : Finset (Fin 4)} {k : Fin 4}
    (hk : ∀ i, i ≠ k → (i ∈ J ↔ k ∉ J)) {M : Matrix (Fin 4) (Fin 4) K}
    (hM : M * signMat K J = signMat K J * M) : (M * M) k k = M k k * M k k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · intro i _ hi
    rw [(apply_eq_zero_of_commute h2 hk hM hi).2, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

end CFSG.ComponentClassification.CatFactsL4U4.BurgD
