module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLf

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSL

open Matrix DiagL

variable {F : Type} [Field F]

@[expose] def mZ (l : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, -l, 0; 0, 0, 0, -1; l, 0, 0, 0; 0, 1, 0, 0]

@[expose] def sZ : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

theorem mZ_mul_mZ {l : F} (hl : l * l = 1) : mZ l * mZ l = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mZ, Matrix.mul_apply, Fin.sum_univ_four, hl]

theorem mZ_uK (l a b : F) : mZ l * (uK l (-a) (-b))ᵀ = uK l a b * mZ l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mZ, uK, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> ring

theorem mZ_lK (l a b : F) : mZ l * (lK l (-a) (-b))ᵀ = lK l a b * mZ l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mZ, lK, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> ring

theorem eK_mZ (l a b : F) : eK l a b * mZ l = mZ l * (eK l a b)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mZ, eK, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> ring

theorem map_uK (σ : F ≃+* F) {l : F} (hσ : σ l = l) (a b : F) :
    (uK l a b).map σ = uK l (σ a) (σ b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uK, hσ]

theorem map_lK (σ : F ≃+* F) {l : F} (hσ : σ l = l) (a b : F) :
    (lK l a b).map σ = lK l (σ a) (σ b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lK, hσ]

theorem sZ_mul_sZ : (sZ : Matrix (Fin 4) (Fin 4) F) * sZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sZ, Matrix.mul_apply, Fin.sum_univ_four]

theorem det_sZ : (sZ : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [sZ, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem sZ_eK (l a b : F) : sZ * eK l a b * sZ = eK l a (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sZ, eK, Matrix.mul_apply, Fin.sum_univ_four]

theorem sZ_kZero (l : F) : sZ * kZero l * sZ = -kZero l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sZ, kZero, Matrix.mul_apply, Fin.sum_univ_four]

theorem det_eK (l a b : F) : (eK l a b).det = (a ^ 2 - l * b ^ 2) ^ 2 := by
  rw [eK, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem eK_comm (l a b c d : F) : eK l a b * eK l c d = eK l c d * eK l a b := by
  rw [eK_mul_eK, eK_mul_eK]
  congr 1 <;> ring

end CSL

end CFSG.ComponentClassification.CatFactsL4U4
