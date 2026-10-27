module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.LieType.Chevalley Matrix

section Basic

variable {F : Type} [Field F]

theorem sl2_exists_entries (B : SL2 F) :
    ∃ a b c d : F, (B : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] ∧ a * d - b * c = 1 := by
  refine ⟨(B : Matrix (Fin 2) (Fin 2) F) 0 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1,
    (B : Matrix (Fin 2) (Fin 2) F) 1 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1,
    Matrix.eta_fin_two _, det_SL2 B⟩

theorem HSL_conj_uSL_A2 (a : Fˣ) (c : F) :
    HSL a * uSL c * (HSL a)⁻¹ = uSL ((a : F) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, uSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem HSL_conj_vSL_A2 (a : Fˣ) (c : F) :
    HSL a * vSL c * (HSL a)⁻¹ = vSL (((a⁻¹ : Fˣ) : F) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem HSL_mul_HSL_A2 (a b : Fˣ) : HSL a * HSL b = HSL (a * b) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm]

theorem HSL_neg_one_eq_neg_one_A2 : (HSL (-1 : Fˣ) : SL2 F) = -1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_HSL]

theorem HSL_neg_one_mul_comm_A2 (g : SL2 F) : HSL (-1 : Fˣ) * g = g * HSL (-1) := by
  rw [HSL_neg_one_eq_neg_one_A2]
  simp

theorem sl2_sq_eq_one_A2 (h2 : (2 : F) ≠ 0) {B : SL2 F} (h : B * B = 1) :
    B = 1 ∨ B = HSL (-1) := by
  obtain ⟨a, b, c, d, hB, hdet⟩ := sl2_exists_entries B
  have h' := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, hB, Matrix.SpecialLinearGroup.coe_one] at h'
  have e00 := congrFun (congrFun h' 0) 0
  have e01 := congrFun (congrFun h' 0) 1
  have e10 := congrFun (congrFun h' 1) 0
  have e11 := congrFun (congrFun h' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  by_cases hs : a + d = 0
  · exfalso
    have hd : d = -a := by linear_combination hs
    rw [hd] at hdet
    have : (2 : F) = 0 := by linear_combination -hdet - e00
    exact h2 this
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    rw [hb, hc] at hdet e00 e11
    simp only [mul_zero, add_zero, sub_zero] at hdet e00 e11
    have ha : a = 1 ∨ a = -1 := by
      have : (a - 1) * (a + 1) = 0 := by linear_combination e00
      rcases mul_eq_zero.1 this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases ha with rfl | rfl
    · left
      have hd1 : d = 1 := by linear_combination hdet
      refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [hB, hb, hc, hd1]
    · right
      have hd1 : d = -1 := by linear_combination -hdet
      refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [hB, hb, hc, hd1, coe_HSL]

end Basic

section Diag

variable {k : Type} [Field k] [IsAlgClosed k]

theorem sl2_exists_conj_diag (h2 : (2 : k) ≠ 0) {B : SL2 k} (h : B * B = HSL (-1)) :
    ∃ (s : SL2 k) (t : kˣ), s * B * s⁻¹ = HSL t := by
  obtain ⟨a, b, c, d, hB, hdet⟩ := sl2_exists_entries B
  have h' := congrArg (fun M : SL2 k => (M : Matrix (Fin 2) (Fin 2) k)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, hB, coe_HSL] at h'
  have e00 := congrFun (congrFun h' 0) 0
  have e01 := congrFun (congrFun h' 0) 1
  have e10 := congrFun (congrFun h' 1) 0
  have e11 := congrFun (congrFun h' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  obtain ⟨i, hi⟩ : ∃ i : k, i ^ 2 = -1 := IsAlgClosed.exists_pow_nat_eq (-1) (by norm_num)
  have hi0 : i ≠ 0 := fun h0 => by
    rw [h0] at hi
    norm_num at hi
  have h2i : 2 * i ≠ 0 := mul_ne_zero h2 hi0
  have hinv : i⁻¹ = -i := by
    field_simp
    linear_combination hi
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · refine ⟨1, Units.mk0 a ?_, ?_⟩
      · intro ha
        rw [ha, hb, hc] at hdet
        simp at hdet
      · rw [inv_one, mul_one, one_mul]
        rw [hb, hc] at hdet
        have ha : a ≠ 0 := fun ha => by rw [ha] at hdet; simp at hdet
        refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [hB, hb, hc, coe_HSL]
        have : d = a⁻¹ := by field_simp; linear_combination hdet
        exact this
    ·
      have had : a + d = 0 := by
        have : b * (a + d) = 0 := by linear_combination e01
        exact (mul_eq_zero.1 this).resolve_left hb
      have hd : d = -a := by linear_combination had
      rw [hc] at e00 hdet
      have hP : (!![b, b / (-(2 * i) * b); i - a, (-i - a) / (-(2 * i) * b)] :
          Matrix (Fin 2) (Fin 2) k).det = 1 := by
        rw [Matrix.det_fin_two_of]
        field_simp
        ring
      let P : SL2 k := ⟨!![b, b / (-(2 * i) * b); i - a, (-i - a) / (-(2 * i) * b)], hP⟩
      have hBP : B * P = P * HSL (Units.mk0 i hi0) := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hB]
        ext r s
        fin_cases r <;> fin_cases s <;>
          simp [P, hc, hd, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two, hinv] <;> field_simp <;>
          first
            | ring1
            | linear_combination e00 - hi
      refine ⟨P⁻¹, Units.mk0 i hi0, ?_⟩
      rw [inv_inv, mul_assoc, hBP, ← mul_assoc, inv_mul_cancel, one_mul]
  ·
    have had : a + d = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_left hc
    have hd : d = -a := by linear_combination had
    have hP : (!![a + i, (a - i) / (2 * i * c); c, c / (2 * i * c)] :
        Matrix (Fin 2) (Fin 2) k).det = 1 := by
      rw [Matrix.det_fin_two_of]
      field_simp
      ring
    let P : SL2 k := ⟨!![a + i, (a - i) / (2 * i * c); c, c / (2 * i * c)], hP⟩
    have hBP : B * P = P * HSL (Units.mk0 i hi0) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hB]
      ext r s
      fin_cases r <;> fin_cases s <;>
        simp [P, hd, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two, hinv] <;> field_simp <;>
        first
          | ring1
          | linear_combination e00 - hi
    refine ⟨P⁻¹, Units.mk0 i hi0, ?_⟩
    rw [inv_inv, mul_assoc, hBP, ← mul_assoc, inv_mul_cancel, one_mul]

end Diag

section Torus

variable {k : Type} [Field k]

theorem sl2_diag_or_anti (h2 : (2 : k) ≠ 0) {s : kˣ} (hs : (s : k) ^ 2 = -1) {B : SL2 k}
    (h : B * HSL s = HSL s * B ∨ B * HSL s = HSL (-1) * (HSL s * B)) :
    (∃ a : kˣ, B = HSL a) ∨ ∃ b : kˣ, B = HSL b * WSL := by
  obtain ⟨a, b, c, d, hB, hdet⟩ := sl2_exists_entries B
  have hs0 : (s : k) ≠ 0 := s.ne_zero
  have hsinv : ((s⁻¹ : kˣ) : k) = -(s : k) := by
    rw [Units.val_inv_eq_inv_val]
    field_simp
    linear_combination hs
  rcases h with h | h
  · left
    have h' := congrArg (fun M : SL2 k => (M : Matrix (Fin 2) (Fin 2) k)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, hB, coe_HSL, hsinv] at h'
    have e01 := congrFun (congrFun h' 0) 1
    have e10 := congrFun (congrFun h' 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
    have hb : b = 0 := by
      have : (2 * s) * b = 0 := by linear_combination -e01
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hs0)
    have hc : c = 0 := by
      have : (2 * s) * c = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hs0)
    rw [hb, hc] at hdet
    simp only [mul_zero, sub_zero] at hdet
    have ha : a ≠ 0 := fun ha => by rw [ha] at hdet; simp at hdet
    refine ⟨Units.mk0 a ha, ?_⟩
    have hd : d = a⁻¹ := by field_simp; linear_combination hdet
    refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [hB, hb, hc, coe_HSL, hd]
  · right
    have h' := congrArg (fun M : SL2 k => (M : Matrix (Fin 2) (Fin 2) k)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, hB, coe_HSL, hsinv] at h'
    have e00 := congrFun (congrFun h' 0) 0
    have e11 := congrFun (congrFun h' 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
    have ha : a = 0 := by
      have : (2 * s) * a = 0 := by linear_combination e00
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hs0)
    have hd : d = 0 := by
      have : (2 * s) * d = 0 := by linear_combination -e11
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hs0)
    rw [ha, hd] at hdet
    simp only [zero_mul, zero_sub] at hdet
    have hb : b ≠ 0 := fun hb => by rw [hb] at hdet; simp at hdet
    refine ⟨Units.mk0 b hb, ?_⟩
    have hc : c = -b⁻¹ := by field_simp; linear_combination -hdet
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [hB, ha, hd, hc, coe_HSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two]

end Torus

end CFSG.ClassicalInvolution.ModelFacts.Levi
