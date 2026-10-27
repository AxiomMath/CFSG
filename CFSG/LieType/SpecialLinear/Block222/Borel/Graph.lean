module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SpecialLinear.BorelStd
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable section

variable (F : Type) [Field F]

theorem permMatrix_rev_mul_self (n : ℕ) :
    LinearFlag.permMatrix n F Fin.revPerm * LinearFlag.permMatrix n F Fin.revPerm = 1 := by
  simp only [LinearFlag.permMatrix_eq]
  calc Equiv.Perm.permMatrix F Fin.revPerm * Equiv.Perm.permMatrix F Fin.revPerm
      = Equiv.Perm.permMatrix F (Fin.revPerm * Fin.revPerm) :=
        (Matrix.permMatrix_mul (R := F) Fin.revPerm Fin.revPerm).symm
    _ = Equiv.Perm.permMatrix F 1 := by
        rw [show (Fin.revPerm : Equiv.Perm (Fin n)) * Fin.revPerm = 1 from
          Equiv.ext fun x => Fin.rev_rev x]
    _ = 1 := Matrix.permMatrix_one

theorem revConj_transpose_two (M : Matrix (Fin 2) (Fin 2) F) :
    LinearFlag.permMatrix 2 F Fin.revPerm * Mᵀ * LinearFlag.permMatrix 2 F Fin.revPerm =
      !![M 1 1, M 0 1; M 1 0, M 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearFlag.permMatrix, Fin.revPerm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply]

theorem revGL_inv (n : ℕ) : (revGL n F)⁻¹ = revGL n F := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inv, coe_revGL]
  exact Matrix.inv_eq_right_inv (permMatrix_rev_mul_self F n)

theorem borelGraph_two_eq_one [CharP F 2] : borelGraph 2 F = 1 := by
  ext g i j
  rw [coe_borelGraph, revGL_inv, coe_revGL, revConj_transpose_two,
    Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]

end

end CFSG.LieType.SpecialLinear
