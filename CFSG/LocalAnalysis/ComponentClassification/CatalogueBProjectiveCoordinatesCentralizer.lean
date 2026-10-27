module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveCoordinatesMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionCommutant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionQuotient

public section

namespace CFSG.ComponentClassification.CatalogueBProjectiveCoordinates

open CatalogueBProjectiveInvolution

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem matrix_mem_centralizer_iff (A B : Matrix.GeneralLinearGroup ι K) :
    B ∈ Subgroup.centralizer {A} ↔
      matrixActionEquiv B ∈ operatorCentralizer (matrixActionEquiv A).toLinearMap := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h v
    have he : matrixActionEquiv B * matrixActionEquiv A =
        matrixActionEquiv A * matrixActionEquiv B := by
      rw [← map_mul, ← map_mul, h]
    exact congrArg (fun C : (ι → K) ≃ₗ[K] (ι → K) => C v) he
  · intro h
    apply matrixActionEquiv.injective
    rw [map_mul, map_mul]
    exact LinearEquiv.ext h

@[expose] def matrixCentralizerEquiv (A : Matrix.GeneralLinearGroup ι K) :
    Subgroup.centralizer {A} ≃* operatorCentralizer (matrixActionEquiv A).toLinearMap where
  toFun B := ⟨matrixActionEquiv B.val, (matrix_mem_centralizer_iff A B.val).mp B.property⟩
  invFun B := ⟨matrixActionEquiv.symm B.val,
    (matrix_mem_centralizer_iff A (matrixActionEquiv.symm B.val)).mpr (by
      rw [matrixActionEquiv_apply_symm_apply]
      exact B.property)⟩
  left_inv B := Subtype.ext (matrixActionEquiv_symm_apply_apply B.val)
  right_inv B := Subtype.ext (matrixActionEquiv_apply_symm_apply B.val)
  map_mul' B C := Subtype.ext (map_mul matrixActionEquiv B.val C.val)

theorem matrixCentralizerEquiv_apply (A : Matrix.GeneralLinearGroup ι K)
    (B : Subgroup.centralizer {A}) :
    (matrixCentralizerEquiv A B).val = matrixActionEquiv B.val := rfl

theorem matrixCentralizerEquiv_symm_apply (A : Matrix.GeneralLinearGroup ι K)
    (B : operatorCentralizer (matrixActionEquiv A).toLinearMap) :
    ((matrixCentralizerEquiv A).symm B).val = matrixActionEquiv.symm B.val := rfl

theorem matrixCentralizerEquiv_symm_apply_apply (A : Matrix.GeneralLinearGroup ι K)
    (B : Subgroup.centralizer {A}) :
    (matrixCentralizerEquiv A).symm (matrixCentralizerEquiv A B) = B :=
  (matrixCentralizerEquiv A).symm_apply_apply B

theorem matrixCentralizerEquiv_apply_symm_apply (A : Matrix.GeneralLinearGroup ι K)
    (B : operatorCentralizer (matrixActionEquiv A).toLinearMap) :
    matrixCentralizerEquiv A ((matrixCentralizerEquiv A).symm B) = B :=
  (matrixCentralizerEquiv A).apply_symm_apply B

theorem scalar_mem_matrixCentralizer (A : Matrix.GeneralLinearGroup ι K) (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar ι c ∈ Subgroup.centralizer {A} :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Matrix.GeneralLinearGroup.scalar_commute c A)

theorem matrixCentralizerEquiv_scalar (A : Matrix.GeneralLinearGroup ι K) (c : Kˣ) :
    matrixCentralizerEquiv A (ordinaryCentralizerScalar A c) =
      operatorCentralizerScalar (matrixActionEquiv A).toLinearMap c := by
  apply Subtype.ext
  exact matrixActionEquiv_scalar c

theorem matrixCentralizerEquiv_symm_scalar (A : Matrix.GeneralLinearGroup ι K) (c : Kˣ) :
    (matrixCentralizerEquiv A).symm
        (operatorCentralizerScalar (matrixActionEquiv A).toLinearMap c) =
      ordinaryCentralizerScalar A c := by
  rw [← matrixCentralizerEquiv_scalar, MulEquiv.symm_apply_apply]

end CFSG.ComponentClassification.CatalogueBProjectiveCoordinates
