module

public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.SectionRank.OddCover

variable {K : Type} [Field K]

@[expose] def cyc4Mat : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]

@[expose] def w02Mat : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1]

@[expose] def w13Mat : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0; 0, 1, 0, 0]

@[expose] def w01Mat : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

theorem cyc4Mat_mul_transpose : cyc4Mat (K := K) * cyc4Matᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc4Mat, Matrix.mul_apply, Fin.sum_univ_four]

theorem cyc4Mat_transpose_mul : cyc4Matᵀ * cyc4Mat (K := K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc4Mat, Matrix.mul_apply, Fin.sum_univ_four]

theorem w02Mat_mul_self : w02Mat (K := K) * w02Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w02Mat, Matrix.mul_apply, Fin.sum_univ_four]

theorem w13Mat_mul_self : w13Mat (K := K) * w13Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w13Mat, Matrix.mul_apply, Fin.sum_univ_four]

theorem w01Mat_mul_self : w01Mat (K := K) * w01Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w01Mat, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def cyc4GL : GL (Fin 4) K :=
  ⟨cyc4Mat, cyc4Matᵀ, cyc4Mat_mul_transpose, cyc4Mat_transpose_mul⟩

@[expose] def w02GL : GL (Fin 4) K := ⟨w02Mat, w02Mat, w02Mat_mul_self, w02Mat_mul_self⟩

@[expose] def w13GL : GL (Fin 4) K := ⟨w13Mat, w13Mat, w13Mat_mul_self, w13Mat_mul_self⟩

@[expose] def w01GL : GL (Fin 4) K := ⟨w01Mat, w01Mat, w01Mat_mul_self, w01Mat_mul_self⟩

theorem coe_cyc4GL : ((cyc4GL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = cyc4Mat := rfl
theorem coe_cyc4GL_inv : ((cyc4GL⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = cyc4Matᵀ := rfl
theorem coe_w02GL : ((w02GL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = w02Mat := rfl
theorem coe_w13GL : ((w13GL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = w13Mat := rfl
theorem coe_w01GL : ((w01GL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = w01Mat := rfl

theorem cyc4GL_conj_diag (d : Fin 4 → Kˣ) :
    cyc4GL * diagHom 4 d * cyc4GL⁻¹ = diagHom 4 ![d 2, d 0, d 1, d 3] := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_cyc4GL, coe_diagHom, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc4Mat, Matrix.mul_apply,
    Matrix.diagonal_apply]

theorem w02GL_conj_diag (d : Fin 4 → Kˣ) :
    w02GL * diagHom 4 d * w02GL⁻¹ = diagHom 4 ![d 2, d 1, d 0, d 3] := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_w02GL, coe_diagHom, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w02Mat, Matrix.mul_apply,
    Matrix.diagonal_apply]

theorem w13GL_conj_diag (d : Fin 4 → Kˣ) :
    w13GL * diagHom 4 d * w13GL⁻¹ = diagHom 4 ![d 0, d 3, d 2, d 1] := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_w13GL, coe_diagHom, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w13Mat, Matrix.mul_apply,
    Matrix.diagonal_apply]

theorem w01GL_conj_diag (d : Fin 4 → Kˣ) :
    w01GL * diagHom 4 d * w01GL⁻¹ = diagHom 4 ![d 1, d 0, d 2, d 3] := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_w01GL, coe_diagHom, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w01Mat, Matrix.mul_apply,
    Matrix.diagonal_apply]

theorem w01GL_conj_cyc4GL : w01GL * cyc4GL * w01GL⁻¹ = (cyc4GL : GL (Fin 4) K)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_w01GL, coe_cyc4GL, coe_cyc4GL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w01Mat, cyc4Mat, Matrix.mul_apply, Fin.sum_univ_four]

end CFSG.ClassicalInvolution.Asc77.SCH
