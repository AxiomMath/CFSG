module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.ComponentClassification.CatalogueBProjectiveCoordinates

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] def matrixActionEquiv :
    Matrix.GeneralLinearGroup ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))

theorem matrixActionEquiv_toLinearMap (A : Matrix.GeneralLinearGroup ι K) :
    (matrixActionEquiv A).toLinearMap = Matrix.mulVecLin A.val := rfl

theorem matrixActionEquiv_apply (A : Matrix.GeneralLinearGroup ι K) (v : ι → K) :
    matrixActionEquiv A v = A.val.mulVec v := rfl

theorem matrixActionEquiv_scalar (c : Kˣ) :
    matrixActionEquiv (Matrix.GeneralLinearGroup.scalar ι c) =
      (LinearEquiv.smulOfUnit c : (ι → K) ≃ₗ[K] (ι → K)) := by
  ext v i
  change (Matrix.scalar ι c.val).mulVec v i = c.val * v i
  simp [Matrix.scalar, Matrix.diagonal, Matrix.mulVec, dotProduct]

theorem matrixActionEquiv_symm_apply_apply (A : Matrix.GeneralLinearGroup ι K) :
    matrixActionEquiv.symm (matrixActionEquiv A) = A :=
  matrixActionEquiv.symm_apply_apply A

theorem matrixActionEquiv_apply_symm_apply (B : (ι → K) ≃ₗ[K] (ι → K)) :
    matrixActionEquiv (matrixActionEquiv.symm B) = B :=
  matrixActionEquiv.apply_symm_apply B

theorem matrixActionEquiv_symm_mulVec (B : (ι → K) ≃ₗ[K] (ι → K)) (v : ι → K) :
    (matrixActionEquiv.symm B).val.mulVec v = B v := by
  rw [← matrixActionEquiv_apply, matrixActionEquiv_apply_symm_apply]

theorem matrixActionEquiv_symm_scalar (c : Kˣ) :
    matrixActionEquiv.symm (LinearEquiv.smulOfUnit c : (ι → K) ≃ₗ[K] (ι → K)) =
      Matrix.GeneralLinearGroup.scalar ι c := by
  rw [← matrixActionEquiv_scalar, matrixActionEquiv_symm_apply_apply]

end CFSG.ComponentClassification.CatalogueBProjectiveCoordinates
