module

public import CFSG.GH74.Generic.Front.InvolutionLA

public section

namespace CFSG.GH74.Generic

@[expose] def diag1 {F : Type*} [Field F] (d : F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal ![d, 1, 1, 1]

theorem diag1_mul {F : Type*} [Field F] (d e : F) : diag1 d * diag1 e = diag1 (d * e) := by
  simp only [diag1, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem diag1_one {F : Type*} [Field F] : diag1 (1 : F) = 1 := by
  simp only [diag1]
  rw [← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

theorem det_diag1 {F : Type*} [Field F] (d : F) : (diag1 d).det = d := by
  simp [diag1, Matrix.det_diagonal, Fin.prod_univ_four]

theorem diag1_mul_diagonal_comm {F : Type*} [Field F] (d : F) :
    diag1 d * Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) =
      Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) * diag1 d := by
  simp only [diag1, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_comm]

theorem exists_conj_diag4_det_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (T : Matrix (Fin 4) (Fin 4) F) (hT : T * T = 1) (hdet : T.det = 1) (h1 : T ≠ 1)
    (hm1 : T ≠ -1) :
    ∃ P : Matrix (Fin 4) (Fin 4) F, P.det = 1 ∧
      T * P = P * Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) := by
  obtain ⟨Q, hQ, hTQ⟩ :=
    exists_conj_diag4 h2 T hT (involution_dim_two h2 (Fintype.card_fin 4) T hT hdet h1 hm1)
  have hdQ : Q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Q).1 hQ).ne_zero
  refine ⟨Q * diag1 (Q.det)⁻¹, ?_, ?_⟩
  · rw [Matrix.det_mul, det_diag1, mul_inv_cancel₀ hdQ]
  · rw [← Matrix.mul_assoc, hTQ, Matrix.mul_assoc, Matrix.mul_assoc, diag1_mul_diagonal_comm]

end CFSG.GH74.Generic
