module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4Mat

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MFO4

open Matrix CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4

variable {F : Type} [Field F]

theorem shape_comm {M : Matrix (Fin 4) (Fin 4) F}
    (h01 : E01 (1 : F) * M = M * E01 1) (h10 : E10 (1 : F) * M = M * E10 1) :
    M 0 1 = 0 ∧ M 0 2 = 0 ∧ M 0 3 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 1 3 = 0 ∧ M 2 0 = 0 ∧
      M 2 1 = 0 ∧ M 3 0 = 0 ∧ M 3 1 = 0 ∧ M 1 1 = M 0 0 := by
  have m10 : M 1 0 = 0 := by
    have h := congrFun (congrFun h01 0) 0
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m11 : M 1 1 = M 0 0 := by
    have h := congrFun (congrFun h01 0) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m12 : M 1 2 = 0 := by
    have h := congrFun (congrFun h01 0) 2
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m13 : M 1 3 = 0 := by
    have h := congrFun (congrFun h01 0) 3
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m20 : M 2 0 = 0 := by
    have h := congrFun (congrFun h01 2) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m30 : M 3 0 = 0 := by
    have h := congrFun (congrFun h01 3) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m01 : M 0 1 = 0 := by
    have h := congrFun (congrFun h10 1) 1
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m02 : M 0 2 = 0 := by
    have h := congrFun (congrFun h10 1) 2
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m03 : M 0 3 = 0 := by
    have h := congrFun (congrFun h10 1) 3
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m21 : M 2 1 = 0 := by
    have h := congrFun (congrFun h10 2) 0
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m31 : M 3 1 = 0 := by
    have h := congrFun (congrFun h10 3) 0
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  exact ⟨m01, m02, m03, m10, m12, m13, m20, m21, m30, m31, m11⟩

theorem shape_anti {M : Matrix (Fin 4) (Fin 4) F}
    (h01 : E01 (1 : F) * M = M * E10 (-1)) (h10 : E10 (1 : F) * M = M * E01 (-1)) :
    M 0 0 = 0 ∧ M 1 1 = 0 ∧ M 0 2 = 0 ∧ M 0 3 = 0 ∧ M 1 2 = 0 ∧ M 1 3 = 0 ∧ M 2 0 = 0 ∧
      M 3 0 = 0 ∧ M 2 1 = 0 ∧ M 3 1 = 0 ∧ M 1 0 = -M 0 1 := by
  have m11 : M 1 1 = 0 := by
    have h := congrFun (congrFun h01 0) 1
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m12 : M 1 2 = 0 := by
    have h := congrFun (congrFun h01 0) 2
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m13 : M 1 3 = 0 := by
    have h := congrFun (congrFun h01 0) 3
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m21 : M 2 1 = 0 := by
    have h := congrFun (congrFun h01 2) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m31 : M 3 1 = 0 := by
    have h := congrFun (congrFun h01 3) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m10 : M 1 0 = -M 0 1 := by
    have h := congrFun (congrFun h01 0) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m00 : M 0 0 = 0 := by
    have h := congrFun (congrFun h10 1) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m02 : M 0 2 = 0 := by
    have h := congrFun (congrFun h10 1) 2
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m03 : M 0 3 = 0 := by
    have h := congrFun (congrFun h10 1) 3
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m20 : M 2 0 = 0 := by
    have h := congrFun (congrFun h10 2) 1
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m30 : M 3 0 = 0 := by
    have h := congrFun (congrFun h10 3) 1
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  exact ⟨m00, m11, m02, m03, m12, m13, m20, m30, m21, m31, m10⟩

theorem eq_spForm_of_shape (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 4) (Fin 4) F} (hdet : M.det ≠ 0)
    (hs : M 0 0 = 0 ∧ M 1 1 = 0 ∧ M 0 2 = 0 ∧ M 0 3 = 0 ∧ M 1 2 = 0 ∧ M 1 3 = 0 ∧ M 2 0 = 0 ∧
      M 3 0 = 0 ∧ M 2 1 = 0 ∧ M 3 1 = 0 ∧ M 1 0 = -M 0 1)
    (c : F) (hc : M = c • Mᵀ) :
    ∃ m n : F, m ≠ 0 ∧ n ≠ 0 ∧
      M = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] := by
  obtain ⟨m00, m11, m02, m03, m12, m13, m20, m30, m21, m31, m10⟩ := hs
  have hm : M 0 1 ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
    fin_cases j <;> simp [h0, m00, m02, m03]
  have hc1 : c = -1 := by
    have h := congrFun (congrFun hc 0) 1
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h
    rw [m10] at h
    have h' : (1 + c) * M 0 1 = 0 := by linear_combination h
    have := (mul_eq_zero.mp h').resolve_right hm
    linear_combination this
  subst hc1
  have m22 : M 2 2 = 0 := by
    have h := congrFun (congrFun hc 2) 2
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h
    have h' : (2 : F) * M 2 2 = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  have m33 : M 3 3 = 0 := by
    have h := congrFun (congrFun hc 3) 3
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h
    have h' : (2 : F) * M 3 3 = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  have m32 : M 3 2 = -M 2 3 := by
    have h := congrFun (congrFun hc 2) 3
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h
    linear_combination h
  have hn : M 2 3 ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero 2 fun j => ?_
    fin_cases j <;> simp [h0, m20, m21, m22]
  refine ⟨M 0 1, M 2 3, hm, hn, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m00, m02, m03, m10, m11, m12, m13, m20, m21, m22, m30, m31,
    m32, m33]

end CFSG.ClassicalInvolution.Q3.Q3MFO4
