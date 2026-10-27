module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixPfaffian

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix

variable {F : Type*} [CommRing F]

theorem congruence_skew (g X : Matrix (Fin 4) (Fin 4) F) (hX : X.transpose = -X) :
    (g * X * g.transpose).transpose = -(g * X * g.transpose) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

private theorem det_four_expansion (g : Matrix (Fin 4) (Fin 4) F) :
    g.det =
      g 0 0 * ((g 1 1 * g 2 2 * g 3 3 - g 1 1 * g 2 3 * g 3 2 -
        g 1 2 * g 2 1 * g 3 3 + g 1 2 * g 2 3 * g 3 1 +
        g 1 3 * g 2 1 * g 3 2 - g 1 3 * g 2 2 * g 3 1)) -
      g 0 1 * ((g 1 0 * g 2 2 * g 3 3 - g 1 0 * g 2 3 * g 3 2 -
        g 1 2 * g 2 0 * g 3 3 + g 1 2 * g 2 3 * g 3 0 +
        g 1 3 * g 2 0 * g 3 2 - g 1 3 * g 2 2 * g 3 0)) +
      g 0 2 * ((g 1 0 * g 2 1 * g 3 3 - g 1 0 * g 2 3 * g 3 1 -
        g 1 1 * g 2 0 * g 3 3 + g 1 1 * g 2 3 * g 3 0 +
        g 1 3 * g 2 0 * g 3 1 - g 1 3 * g 2 1 * g 3 0)) -
      g 0 3 * ((g 1 0 * g 2 1 * g 3 2 - g 1 0 * g 2 2 * g 3 1 -
        g 1 1 * g 2 0 * g 3 2 + g 1 1 * g 2 2 * g 3 0 +
        g 1 2 * g 2 0 * g 3 1 - g 1 2 * g 2 1 * g 3 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  ring

theorem pfaffian_congruence_skewMatrix (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    pfaffian (g * skewMatrix a b c d e f * g.transpose) =
      g.det * pfaffian (skewMatrix a b c d e f) := by
  rw [det_four_expansion]
  simp [pfaffian, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

private theorem sharp_congruence_entry_00 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 0 0 =
      (g.det • sharp (skewMatrix a b c d e f)) 0 0 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_01 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 0 1 =
      (g.det • sharp (skewMatrix a b c d e f)) 0 1 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_02 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 0 2 =
      (g.det • sharp (skewMatrix a b c d e f)) 0 2 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_03 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 0 3 =
      (g.det • sharp (skewMatrix a b c d e f)) 0 3 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_10 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 1 0 =
      (g.det • sharp (skewMatrix a b c d e f)) 1 0 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_11 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 1 1 =
      (g.det • sharp (skewMatrix a b c d e f)) 1 1 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_12 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 1 2 =
      (g.det • sharp (skewMatrix a b c d e f)) 1 2 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_13 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 1 3 =
      (g.det • sharp (skewMatrix a b c d e f)) 1 3 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_20 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 2 0 =
      (g.det • sharp (skewMatrix a b c d e f)) 2 0 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_21 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 2 1 =
      (g.det • sharp (skewMatrix a b c d e f)) 2 1 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_22 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 2 2 =
      (g.det • sharp (skewMatrix a b c d e f)) 2 2 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_23 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 2 3 =
      (g.det • sharp (skewMatrix a b c d e f)) 2 3 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_30 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 3 0 =
      (g.det • sharp (skewMatrix a b c d e f)) 3 0 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_31 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 3 1 =
      (g.det • sharp (skewMatrix a b c d e f)) 3 1 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_32 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 3 2 =
      (g.det • sharp (skewMatrix a b c d e f)) 3 2 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem sharp_congruence_entry_33 (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    (g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g) 3 3 =
      (g.det • sharp (skewMatrix a b c d e f)) 3 3 := by
  rw [det_four_expansion]
  simp [sharp, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem sharp_congruence_skewMatrix (g : Matrix (Fin 4) (Fin 4) F)
    (a b c d e f : F) :
    g.transpose * sharp (g * skewMatrix a b c d e f * g.transpose) * g =
      g.det • sharp (skewMatrix a b c d e f) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact sharp_congruence_entry_00 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_01 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_02 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_03 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_10 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_11 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_12 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_13 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_20 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_21 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_22 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_23 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_30 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_31 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_32 _ _ _ _ _ _ _
  · exact sharp_congruence_entry_33 _ _ _ _ _ _ _

section Field

variable {K : Type*} [Field K]

theorem pfaffian_congruence (h2 : (2 : K) ≠ 0)
    (g : Matrix (Fin 4) (Fin 4) K) {X : Matrix (Fin 4) (Fin 4) K}
    (hX : X.transpose = -X) :
    pfaffian (g * X * g.transpose) = g.det * pfaffian X := by
  rw [skew_eq_skewMatrix h2 hX]
  exact pfaffian_congruence_skewMatrix _ _ _ _ _ _ _

theorem sharp_congruence (h2 : (2 : K) ≠ 0)
    (g : Matrix.GeneralLinearGroup (Fin 4) K) {X : Matrix (Fin 4) (Fin 4) K}
    (hX : X.transpose = -X) :
    sharp (g.val * X * g.val.transpose) =
      g.val.det • ((g⁻¹).val.transpose * sharp X * (g⁻¹).val) := by
  have hpoly : g.val.transpose * sharp (g.val * X * g.val.transpose) * g.val =
      g.val.det • sharp X := by
    rw [skew_eq_skewMatrix h2 hX]
    exact sharp_congruence_skewMatrix _ _ _ _ _ _ _
  have h := congrArg (fun A => (g⁻¹).val.transpose * A * (g⁻¹).val) hpoly
  have ht : (g⁻¹).val.transpose * g.val.transpose = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc (g⁻¹).val.transpose g.val.transpose,
    ht, Matrix.one_mul, Units.mul_inv, Matrix.mul_one, Matrix.mul_smul,
    Matrix.smul_mul] using h

theorem skew_four_pfaffian_identities (h2 : (2 : K) ≠ 0)
    (X : Matrix (Fin 4) (Fin 4) K) (hX : X.transpose = -X) :
    sharp (sharp X) = X ∧ pfaffian (sharp X) = pfaffian X ∧
      X * sharp X = -pfaffian X • (1 : Matrix (Fin 4) (Fin 4) K) ∧
      sharp X * X = -pfaffian X • (1 : Matrix (Fin 4) (Fin 4) K) ∧
      X.det = pfaffian X ^ 2 ∧
      (∀ Y : Matrix (Fin 4) (Fin 4) K, Y.transpose = -Y →
        X * sharp Y + Y * sharp X =
          -(pfaffian (X + Y) - pfaffian X - pfaffian Y) •
            (1 : Matrix (Fin 4) (Fin 4) K)) ∧
      (∀ g : Matrix.GeneralLinearGroup (Fin 4) K,
        pfaffian (g.val * X * g.val.transpose) = g.val.det * pfaffian X ∧
          sharp (g.val * X * g.val.transpose) =
            g.val.det • ((g⁻¹).val.transpose * sharp X * (g⁻¹).val)) :=
  ⟨sharp_sharp h2 hX, pfaffian_sharp h2 hX, mul_sharp h2 hX, sharp_mul h2 hX,
    skew_det h2 hX, fun _ hY => polarized_product h2 hX hY,
    fun g => ⟨pfaffian_congruence h2 g.val hX, sharp_congruence h2 g hX⟩⟩

end Field

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
