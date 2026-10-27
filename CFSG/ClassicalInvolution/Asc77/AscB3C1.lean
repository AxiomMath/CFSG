module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpStd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpAlg

public section

namespace CFSG.ClassicalInvolution.Asc77.B3C

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp (blk mat_blk)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

@[expose] def kronMat (A : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks (A 0 0 • 1) (A 0 1 • 1) (A 1 0 • 1) (A 1 1 • 1)

theorem kronMat_symp (A : SL(2, F)) :
    (kronMat (A : Matrix (Fin 2) (Fin 2) F))ᵀ * gram F 2 *
      kronMat (A : Matrix (Fin 2) (Fin 2) F) = gram F 2 := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two] at this
    exact this
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [kronMat, gram, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.transpose_apply]
  all_goals first | ring1 | linear_combination hdet | linear_combination -hdet

theorem kronMat_mul (A B : SL(2, F)) :
    kronMat ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      kronMat (A : Matrix (Fin 2) (Fin 2) F) * kronMat (B : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [kronMat, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.SpecialLinearGroup.coe_mul, Fin.sum_univ_two]

theorem kronMat_one : kronMat ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [kronMat, Matrix.fromBlocks]

@[expose] noncomputable def kron2 : SL(2, F) →* StatedSp 2 F where
  toFun A := ofSymplecticMat (kronMat (A : Matrix (Fin 2) (Fin 2) F)) (kronMat_symp A)
  map_one' := by
    apply mat_injective
    rw [mat_ofSymplecticMat, map_one]
    exact kronMat_one
  map_mul' A B := by
    apply mat_injective
    rw [mat_ofSymplecticMat, map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat]
    exact kronMat_mul A B

theorem mat_kron2 (A : SL(2, F)) : mat 2 F (kron2 A) = kronMat (A : Matrix (Fin 2) (Fin 2) F) :=
  rfl

@[expose] def Pmat (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![1, 1; 0, 0] !![0, 0; 2⁻¹, -2⁻¹] !![0, 0; -1, 1] !![2⁻¹, 2⁻¹; 0, 0]

theorem Pmat_symp (h2 : (2 : F) ≠ 0) : (Pmat F)ᵀ * gram F 2 * Pmat F = gram F 2 := by
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Pmat, gram, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.transpose_apply]
  all_goals first | ring1 | linear_combination h22 | linear_combination -h22

@[expose] noncomputable def Pel (h2 : (2 : F) ≠ 0) : StatedSp 2 F :=
  ofSymplecticMat (Pmat F) (Pmat_symp h2)

theorem mat_Pel (h2 : (2 : F) ≠ 0) : mat 2 F (Pel h2) = Pmat F := rfl

@[expose] noncomputable def twShort (h2 : (2 : F) ≠ 0) : SL(2, F) →* StatedSp 2 F :=
  (MulAut.conj (Pel h2)⁻¹).toMonoidHom.comp kron2

theorem twShort_apply (h2 : (2 : F) ≠ 0) (A : SL(2, F)) :
    twShort h2 A = (Pel h2)⁻¹ * kron2 A * Pel h2 := by
  simp [twShort]

@[expose] noncomputable def rho0 (h2 : (2 : F) ≠ 0) : SL(2, F) :=
  ⟨!![0, -2⁻¹; 2, 0], by
    rw [Matrix.det_fin_two_of]
    have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    linear_combination h22⟩

@[expose] noncomputable def rho1 (h2 : (2 : F) ≠ 0) : SL(2, F) :=
  ⟨!![0, 2⁻¹; -2, 0], by
    rw [Matrix.det_fin_two_of]
    have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    linear_combination h22⟩

theorem rho0_sq (h2 : (2 : F) ≠ 0) :
    ((rho0 h2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * rho0 h2 = -1 := by
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  show (!![0, -2⁻¹; 2, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -2⁻¹; 2, 0] = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h22

theorem rho1_sq (h2 : (2 : F) ≠ 0) :
    ((rho1 h2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * rho1 h2 = -1 := by
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  show (!![0, 2⁻¹; -2, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 2⁻¹; -2, 0] = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h22

@[expose] def rTmat (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![0, -1; 1, 0] 0 0 !![0, -1; 1, 0]

theorem rTmat_symp : (rTmat F)ᵀ * gram F 2 * rTmat F = gram F 2 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rTmat, gram, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.transpose_apply]

@[expose] noncomputable def rT : StatedSp 2 F := ofSymplecticMat (rTmat F) rTmat_symp

theorem Pel_mul_dB (h2 : (2 : F) ≠ 0) :
    Pel h2 * blk F (rho0 h2) (rho1 h2) = rT * Pel h2 := by
  apply mat_injective
  rw [map_mul, map_mul, mat_Pel, mat_blk]
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rT, rTmat, Pmat, rho0, rho1, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.diagonal_apply, mat_ofSymplecticMat]
  all_goals first | ring1 | linear_combination h22

theorem kron2_comm_rT (A : SL(2, F)) : kron2 A * rT = rT * kron2 A := by
  apply mat_injective
  rw [map_mul, map_mul, mat_kron2]
  show kronMat (A : Matrix (Fin 2) (Fin 2) F) * rTmat F =
    rTmat F * kronMat (A : Matrix (Fin 2) (Fin 2) F)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [kronMat, rTmat, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply]

theorem twShort_comm_dB (h2 : (2 : F) ≠ 0) (A : SL(2, F)) :
    twShort h2 A * blk F (rho0 h2) (rho1 h2) = blk F (rho0 h2) (rho1 h2) * twShort h2 A := by
  have hP := Pel_mul_dB h2
  have hk := kron2_comm_rT A
  have hdB : blk F (rho0 h2) (rho1 h2) = (Pel h2)⁻¹ * rT * Pel h2 := by
    rw [mul_assoc, ← hP]
    group
  rw [twShort_apply, hdB]
  calc (Pel h2)⁻¹ * kron2 A * Pel h2 * ((Pel h2)⁻¹ * rT * Pel h2)
      = (Pel h2)⁻¹ * (kron2 A * rT) * Pel h2 := by group
    _ = (Pel h2)⁻¹ * (rT * kron2 A) * Pel h2 := by rw [hk]
    _ = (Pel h2)⁻¹ * rT * Pel h2 * ((Pel h2)⁻¹ * kron2 A * Pel h2) := by group

end CFSG.ClassicalInvolution.Asc77.B3C
