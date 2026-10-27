module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLTwo

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL

variable {F : Type} [Field F]

theorem commute_tMat_entries {T : Matrix (Fin 3) (Fin 3) F} {a b c : F}
    (h : T * tMat a b c = tMat a b c * T) :
    a * T 1 0 + c * T 2 0 = 0 ∧ a * T 0 0 = a * T 1 1 + c * T 2 1 ∧ b * T 2 0 = 0 ∧
      a * T 1 0 = b * T 2 1 ∧ c * T 1 0 + b * (T 1 1 - T 2 2) = 0 ∧ a * T 2 0 = 0 ∧
      c * T 2 0 + b * T 2 1 = 0 := by
  have e : ∀ i j, (T * tMat a b c) i j = (tMat a b c * T) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, tMat, -mul_eq_zero, -zero_eq_mul] at e00 e01 e10 e11
  simp [Matrix.mul_apply, Fin.sum_univ_three, tMat, -mul_eq_zero, -zero_eq_mul] at e12 e21 e22
  refine ⟨by linear_combination -e00, by linear_combination e01, by linear_combination e10,
    by linear_combination e11, by linear_combination e12, by linear_combination e21,
    by linear_combination e22⟩

theorem commute_tMat_pair {T : Matrix (Fin 3) (Fin 3) F} {a b c a' b' c' : F}
    (hD : a * b' - a' * b ≠ 0) (h : T * tMat a b c = tMat a b c * T)
    (h' : T * tMat a' b' c' = tMat a' b' c' * T) :
    T 1 0 = 0 ∧ T 2 0 = 0 ∧ T 2 1 = 0 ∧ T 0 0 = T 1 1 ∧ T 1 1 = T 2 2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := commute_tMat_entries h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := commute_tMat_entries h'
  have h20 : T 2 0 = 0 := by
    apply mul_left_cancel₀ hD
    linear_combination b' * e6 - b * f6
  have h21 : T 2 1 = 0 := by
    apply mul_left_cancel₀ hD
    linear_combination a * f7 - a' * e7 - (a * c' - a' * c) * h20
  have h10 : T 1 0 = 0 := by
    apply mul_left_cancel₀ hD
    linear_combination b' * e1 - b * f1 - (b' * c - b * c') * h20
  refine ⟨h10, h20, h21, ?_, ?_⟩
  · apply sub_eq_zero.1
    apply mul_left_cancel₀ hD
    linear_combination b' * e2 - b * f2 + (b' * c - b * c') * h21
  · apply sub_eq_zero.1
    apply mul_left_cancel₀ hD
    linear_combination a * f5 - a' * e5 - (a * c' - a' * c) * h10

theorem pow_four_of_tri (h2 : (2 : F) = 0) {T : Matrix (Fin 3) (Fin 3) F} (h10 : T 1 0 = 0)
    (h20 : T 2 0 = 0) (h21 : T 2 1 = 0) (h01 : T 0 0 = T 1 1) (h12 : T 1 1 = T 2 2) :
    T ^ 4 = (T 0 0 ^ 4) • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have hd1 : T 1 1 = T 0 0 := h01.symm
  have hd2 : T 2 2 = T 0 0 := h12.symm.trans hd1
  have hT : T = !![T 0 0, T 0 1, T 0 2; 0, T 0 0, T 1 2; 0, 0, T 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h20, h21, hd1, hd2]
  have h4 : (4 : F) = 0 := by rw [show (4 : F) = 2 * 2 by norm_num, h2, zero_mul]
  have h6 : (6 : F) = 0 := by rw [show (6 : F) = 2 * 3 by norm_num, h2, zero_mul]
  generalize T 0 0 = l at hT ⊢
  generalize T 0 1 = p at hT
  generalize T 0 2 = q at hT
  generalize T 1 2 = r at hT
  subst hT
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;> ring_nf <;> simp [h4, h6]

theorem eq_smul_one_of_tri_odd (h2 : (2 : F) = 0) {T : Matrix (Fin 3) (Fin 3) F} {r : ℕ}
    (hr : Odd r) (hT : T ^ r = 1) (h10 : T 1 0 = 0) (h20 : T 2 0 = 0) (h21 : T 2 1 = 0)
    (h01 : T 0 0 = T 1 1) (h12 : T 1 1 = T 2 2) : ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have h4 := pow_four_of_tri h2 h10 h20 h21 h01 h12
  generalize T 0 0 ^ 4 = μ at h4
  obtain ⟨k, rfl⟩ := hr
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hr : 2 * k + 1 = 4 * m + 1 := by omega
    rw [hr, pow_add, pow_mul, h4, pow_one, smul_pow, one_pow, smul_mul_assoc, one_mul] at hT
    have hμ : μ ^ m ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hT
      exact zero_ne_one hT
    refine ⟨(μ ^ m)⁻¹, ?_⟩
    calc T = (μ ^ m)⁻¹ • (μ ^ m • T) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = _ := by rw [hT]
  · have hr : 2 * k + 1 = 4 * m + 3 := by omega
    rw [hr, pow_add, pow_mul, h4, smul_pow, one_pow, smul_mul_assoc, one_mul] at hT
    have hμ : μ ^ m ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hT
      exact zero_ne_one hT
    have h3 : T ^ 3 = (μ ^ m)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) F) := by
      calc T ^ 3 = (μ ^ m)⁻¹ • (μ ^ m • T ^ 3) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
        _ = _ := by rw [hT]
    have hν : (μ ^ m)⁻¹ ≠ 0 := inv_ne_zero hμ
    have h44 : T ^ 4 = (μ ^ m)⁻¹ • T := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, smul_mul_assoc, one_mul]
    rw [h4] at h44
    refine ⟨((μ ^ m)⁻¹)⁻¹ * μ, ?_⟩
    calc T = ((μ ^ m)⁻¹)⁻¹ • ((μ ^ m)⁻¹ • T) := by rw [smul_smul, inv_mul_cancel₀ hν, one_smul]
      _ = _ := by rw [← h44, smul_smul]

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL
