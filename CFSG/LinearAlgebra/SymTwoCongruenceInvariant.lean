module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.ClassicalGroups.Alternating.TransvectionGeneration

public section

open Matrix

namespace CFSG.LinearAlgebra

private lemma mem_add_lower_conj {K : Type*} [Field K] [CharP K 2]
    {S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)} {s : Matrix (Fin 2) (Fin 2) K}
    (hs : sᵀ = s) (hsS : s ∈ S)
    (hinv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ t ∈ S,
      (g : Matrix (Fin 2) (Fin 2) K) * t * (g : Matrix (Fin 2) (Fin 2) K)ᵀ ∈ S) :
    ∀ μ : K, !![0, s 0 0 * μ; s 0 0 * μ, s 0 0 * μ ^ 2] ∈ S := by
  intro μ
  let g : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 0; μ, 1], by simp [Matrix.det_fin_two]⟩
  have hgc : (g : Matrix (Fin 2) (Fin 2) K) = !![1, 0; μ, 1] := rfl
  have hmem : (g : Matrix (Fin 2) (Fin 2) K) * s * (g : Matrix (Fin 2) (Fin 2) K)ᵀ + s ∈ S :=
    S.add_mem (hinv g s hsS) hsS
  have h10 : s 1 0 = s 0 1 := by
    have h := congrFun (congrFun hs 0) 1
    simpa [Matrix.transpose_apply] using h
  have htr : (!![1, 0; μ, 1] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![1, μ; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have e : (g : Matrix (Fin 2) (Fin 2) K) * s * (g : Matrix (Fin 2) (Fin 2) K)ᵀ + s =
      !![0, s 0 0 * μ; s 0 0 * μ, s 0 0 * μ ^ 2] := by
    rw [hgc, htr, Matrix.eta_fin_two s, h10]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero, add_assoc] <;> ring_nf
    simp [CharTwo.two_eq_zero]
  rwa [e] at hmem

private lemma mem_smul_E22 {K : Type*} [Field K] [Finite K] [CharP K 2]
    {S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)} {a : K} (ha : a ≠ 0)
    (hinv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ t ∈ S,
      (g : Matrix (Fin 2) (Fin 2) K) * t * (g : Matrix (Fin 2) (Fin 2) K)ᵀ ∈ S)
    {lam nu : K} (hdet : lam * nu = 1) (hnu : nu * nu ≠ 1)
    (hT : ∀ μ : K, !![0, a * μ; a * μ, a * μ ^ 2] ∈ S) :
    ∀ κ : K, !![0, 0; 0, κ] ∈ S := by
  have hone : (1 : K) + nu * nu ≠ 0 := by
    intro h
    exact hnu (CharTwo.add_eq_zero.mp h).symm
  have hc : a * (1 + nu * nu) ≠ 0 := mul_ne_zero ha hone
  intro κ
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' (R := K) (κ / (a * (1 + nu * nu)))
  have hμ' : a * (1 + nu * nu) * μ ^ 2 = κ := by
    rw [pow_two, ← hμ]
    exact mul_div_cancel₀ κ hc
  have hentry : a * μ ^ 2 * (1 + nu * nu) = κ := by
    rw [← hμ']
    ring
  let h : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![lam, 0; 0, nu], by rw [Matrix.det_fin_two]; simpa using hdet⟩
  have hhc : (h : Matrix (Fin 2) (Fin 2) K) = !![lam, 0; 0, nu] := rfl
  have htr : (!![lam, 0; 0, nu] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![lam, 0; 0, nu] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hTμ := hT μ
  have hmem : !![0, a * μ; a * μ, a * μ ^ 2] +
      (h : Matrix (Fin 2) (Fin 2) K) * !![0, a * μ; a * μ, a * μ ^ 2] *
        (h : Matrix (Fin 2) (Fin 2) K)ᵀ ∈ S :=
    S.add_mem hTμ (hinv h _ hTμ)
  have e : !![0, a * μ; a * μ, a * μ ^ 2] +
      (h : Matrix (Fin 2) (Fin 2) K) * !![0, a * μ; a * μ, a * μ ^ 2] *
        (h : Matrix (Fin 2) (Fin 2) K)ᵀ = !![0, 0; 0, κ] := by
    rw [hhc, htr]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CharTwo.add_self_eq_zero, add_assoc] <;> ring_nf
    all_goals
      first
      | rw [← hentry]; ring
      | rw [mul_assoc (a * μ) lam nu, hdet, mul_one]; exact CharTwo.add_self_eq_zero _
      | rw [mul_assoc (a * μ) nu lam, mul_comm nu lam, hdet, mul_one]
        exact CharTwo.add_self_eq_zero _
  rwa [e] at hmem

private lemma mem_smul_J {K : Type*} [Field K] [CharP K 2]
    {S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)} {a : K} (ha : a ≠ 0)
    (hT : ∀ μ : K, !![0, a * μ; a * μ, a * μ ^ 2] ∈ S)
    (hE22 : ∀ κ : K, !![0, 0; 0, κ] ∈ S) :
    ∀ κ : K, !![0, κ; κ, 0] ∈ S := by
  intro κ
  have hμ : a * (κ / a) = κ := mul_div_cancel₀ κ ha
  have hmem : !![0, a * (κ / a); a * (κ / a), a * (κ / a) ^ 2] +
      !![0, 0; 0, a * (κ / a) ^ 2] ∈ S := S.add_mem (hT _) (hE22 _)
  have e : !![0, a * (κ / a); a * (κ / a), a * (κ / a) ^ 2] +
      !![0, 0; 0, a * (κ / a) ^ 2] = !![0, κ; κ, 0] := by
    rw [hμ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]
  rwa [e] at hmem

private lemma mem_smul_E11 {K : Type*} [Field K] [CharP K 2]
    {S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)}
    (hinv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ t ∈ S,
      (g : Matrix (Fin 2) (Fin 2) K) * t * (g : Matrix (Fin 2) (Fin 2) K)ᵀ ∈ S)
    (hE22 : ∀ κ : K, !![0, 0; 0, κ] ∈ S) :
    ∀ κ : K, !![κ, 0; 0, 0] ∈ S := by
  intro κ
  let w : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two]; simp [CharTwo.neg_eq]⟩
  have hwc : (w : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl
  have hmem : (w : Matrix (Fin 2) (Fin 2) K) * !![0, 0; 0, κ] *
      (w : Matrix (Fin 2) (Fin 2) K)ᵀ ∈ S := hinv w _ (hE22 κ)
  have htr : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have e : (w : Matrix (Fin 2) (Fin 2) K) * !![0, 0; 0, κ] *
      (w : Matrix (Fin 2) (Fin 2) K)ᵀ = !![κ, 0; 0, 0] := by
    rw [hwc, htr]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rwa [e] at hmem

private lemma mem_of_symmetric_parts {K : Type*} [Field K]
    {S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)}
    (h11 : ∀ κ : K, !![κ, 0; 0, 0] ∈ S)
    (hJ : ∀ κ : K, !![0, κ; κ, 0] ∈ S)
    (h22 : ∀ κ : K, !![0, 0; 0, κ] ∈ S)
    (t : Matrix (Fin 2) (Fin 2) K) (ht : tᵀ = t) : t ∈ S := by
  have h10 : t 1 0 = t 0 1 := by
    have h := congrFun (congrFun ht 0) 1
    simpa [Matrix.transpose_apply] using h
  have ht' : t = !![t 0 0, t 0 1; t 0 1, t 1 1] := by
    conv_lhs => rw [Matrix.eta_fin_two t]
    rw [h10]
  rw [ht']
  have hsum : !![t 0 0, t 0 1; t 0 1, t 1 1] =
      !![t 0 0, 0; 0, 0] + !![0, t 0 1; t 0 1, 0] + !![0, 0; 0, t 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hsum]
  exact S.add_mem (S.add_mem (h11 _) (hJ _)) (h22 _)

private lemma sym_mem_of_diag_ne_zero {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 2 < Nat.card K) {S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)}
    {s : Matrix (Fin 2) (Fin 2) K} (hs : sᵀ = s) (hsS : s ∈ S)
    (hinv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ t ∈ S,
      (g : Matrix (Fin 2) (Fin 2) K) * t * (g : Matrix (Fin 2) (Fin 2) K)ᵀ ∈ S)
    (ha : s 0 0 ≠ 0) : ∀ t : Matrix (Fin 2) (Fin 2) K, tᵀ = t → t ∈ S := by
  obtain ⟨lam, hlam0, hlam1⟩ :=
    CFSG.ClassicalGroups.Alternating.exists_ne_zero_ne_one_of_two_lt_card hK
  set nu : K := lam⁻¹ with hnu_def
  have hdet : lam * nu = 1 := by
    rw [hnu_def]
    exact mul_inv_cancel₀ hlam0
  have hnu1 : nu ≠ 1 := by
    intro h
    exact hlam1 (by rw [h, mul_one] at hdet; exact hdet)
  have hnu2 : nu * nu ≠ 1 := by
    intro h
    apply hnu1
    have h2 : nu ^ 2 = 1 := by rw [pow_two]; exact h
    rcases sq_eq_one_iff.mp h2 with h' | h'
    · exact h'
    · rwa [CharTwo.neg_eq] at h'
  have hT := mem_add_lower_conj hs hsS hinv
  have hE22 := mem_smul_E22 ha hinv hdet hnu2 hT
  exact fun t ht => mem_of_symmetric_parts (mem_smul_E11 hinv hE22) (mem_smul_J ha hT hE22)
    hE22 t ht

theorem sym_two_congr_invariant_dichotomy {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 2 < Nat.card K) (S : AddSubgroup (Matrix (Fin 2) (Fin 2) K))
    (hsym : ∀ s ∈ S, sᵀ = s)
    (hinv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ s ∈ S,
      (g : Matrix (Fin 2) (Fin 2) K) * s * (g : Matrix (Fin 2) (Fin 2) K)ᵀ ∈ S) :
    (∀ s ∈ S, s 0 0 = 0 ∧ s 1 1 = 0) ∨
      ∀ s : Matrix (Fin 2) (Fin 2) K, sᵀ = s → s ∈ S := by
  by_cases hzero : ∀ s ∈ S, s 0 0 = 0 ∧ s 1 1 = 0
  · exact Or.inl hzero
  · right
    push Not at hzero
    obtain ⟨s, hsS, hsne⟩ := hzero
    have hsne' : s 0 0 ≠ 0 ∨ s 1 1 ≠ 0 := by
      by_cases h : s 0 0 = 0
      · exact Or.inr (hsne h)
      · exact Or.inl h
    have hs : sᵀ = s := hsym s hsS
    rcases hsne' with ha | hc
    · exact sym_mem_of_diag_ne_zero hK hs hsS hinv ha
    · let w : Matrix.SpecialLinearGroup (Fin 2) K :=
        ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two]; simp [CharTwo.neg_eq]⟩
      have hwc : (w : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl
      have hmem : (w : Matrix (Fin 2) (Fin 2) K) * s *
          (w : Matrix (Fin 2) (Fin 2) K)ᵀ ∈ S := hinv w s hsS
      have hsym' : ((w : Matrix (Fin 2) (Fin 2) K) * s *
          (w : Matrix (Fin 2) (Fin 2) K)ᵀ)ᵀ =
          (w : Matrix (Fin 2) (Fin 2) K) * s * (w : Matrix (Fin 2) (Fin 2) K)ᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hs,
          mul_assoc]
      have h00 : ((w : Matrix (Fin 2) (Fin 2) K) * s *
          (w : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 0 = s 1 1 := by
        rw [hwc, Matrix.eta_fin_two s]
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      exact sym_mem_of_diag_ne_zero hK hsym' hmem hinv (by rw [h00]; exact hc)

end CFSG.LinearAlgebra
