module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitMatrix

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

@[expose] def splitDiagonalScalars (r s : ℕ) :
    Kˣ →* (Matrix.GeneralLinearGroup (Fin r) K × Matrix.GeneralLinearGroup (Fin s) K) :=
  (Matrix.GeneralLinearGroup.scalar (Fin r)).prod
    (Matrix.GeneralLinearGroup.scalar (Fin s))

theorem splitDiagonalScalars_apply (r s : ℕ) (c : Kˣ) :
    splitDiagonalScalars r s c =
      (Matrix.GeneralLinearGroup.scalar (Fin r) c,
        Matrix.GeneralLinearGroup.scalar (Fin s) c) := rfl

theorem mem_splitDiagonalScalars_range (r s : ℕ)
    (B : Matrix.GeneralLinearGroup (Fin r) K × Matrix.GeneralLinearGroup (Fin s) K) :
    B ∈ (splitDiagonalScalars r s).range ↔
      ∃ c : Kˣ, (Matrix.GeneralLinearGroup.scalar (Fin r) c,
        Matrix.GeneralLinearGroup.scalar (Fin s) c) = B := Iff.rfl

theorem splitDiagonalScalars_range_le_center (r s : ℕ) :
    (splitDiagonalScalars (K := K) r s).range ≤
      Subgroup.center
        (Matrix.GeneralLinearGroup (Fin r) K × Matrix.GeneralLinearGroup (Fin s) K) := by
  rintro B ⟨c, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro D
  exact Prod.ext (Matrix.GeneralLinearGroup.scalar_commute c D.1).symm
    (Matrix.GeneralLinearGroup.scalar_commute c D.2).symm

instance splitDiagonalScalars_range_normal (r s : ℕ) :
    (splitDiagonalScalars (K := K) r s).range.Normal :=
  Subgroup.normal_of_le_center (splitDiagonalScalars_range_le_center r s)

theorem matrixCentralizerSplitEquiv_scalarRange (A : Matrix.GeneralLinearGroup ι K) (b : Kˣ)
    (htwo : (2 : K) ≠ 0)
    (hsquare : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι (b ^ 2)) :
    (ordinaryCentralizerScalar A).range.map
        (matrixCentralizerSplitEquiv A b htwo hsquare).toMonoidHom =
      (splitDiagonalScalars (positiveMatrixDimension A b.val)
        (negativeMatrixDimension A b.val)).range :=
  scalarRange_map_of_compatible A (matrixCentralizerSplitEquiv A b htwo hsquare)
    (splitDiagonalScalars (positiveMatrixDimension A b.val) (negativeMatrixDimension A b.val))
    (matrixCentralizerSplitEquiv_scalar A b htwo hsquare)

@[expose] def projectiveSplitQuotientEquiv (A : Matrix.GeneralLinearGroup ι K) (b : Kˣ)
    (htwo : (2 : K) ≠ 0)
    (hsquare : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι (b ^ 2)) :
    (ordinaryCentralizerProjection A).range ≃*
      ((Matrix.GeneralLinearGroup (Fin (positiveMatrixDimension A b.val)) K ×
        Matrix.GeneralLinearGroup (Fin (negativeMatrixDimension A b.val)) K) ⧸
          (splitDiagonalScalars (positiveMatrixDimension A b.val)
            (negativeMatrixDimension A b.val)).range) :=
  ordinaryCentralizerCoordinateQuotientEquiv A (matrixCentralizerSplitEquiv A b htwo hsquare)
    (splitDiagonalScalars (positiveMatrixDimension A b.val) (negativeMatrixDimension A b.val))
    (matrixCentralizerSplitEquiv_scalar A b htwo hsquare)

theorem projectiveSplitQuotientEquiv_symm_mk (A : Matrix.GeneralLinearGroup ι K) (b : Kˣ)
    (htwo : (2 : K) ≠ 0)
    (hsquare : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι (b ^ 2))
    (B : Subgroup.centralizer {A}) :
    ((projectiveSplitQuotientEquiv A b htwo hsquare).symm
      (QuotientGroup.mk (matrixCentralizerSplitEquiv A b htwo hsquare B))).val =
        ordinaryCentralizerProjection A B := by
  change ((ordinaryCentralizerScalarQuotientEquiv A)
    ((QuotientGroup.congr (ordinaryCentralizerScalar A).range
      (splitDiagonalScalars (positiveMatrixDimension A b.val)
        (negativeMatrixDimension A b.val)).range
      (matrixCentralizerSplitEquiv A b htwo hsquare)
      (matrixCentralizerSplitEquiv_scalarRange A b htwo hsquare)).symm
        (QuotientGroup.mk (matrixCentralizerSplitEquiv A b htwo hsquare B)))).val = _
  rw [← QuotientGroup.congr_mk (ordinaryCentralizerScalar A).range
    (splitDiagonalScalars (positiveMatrixDimension A b.val) (negativeMatrixDimension A b.val)).range
    (matrixCentralizerSplitEquiv A b htwo hsquare)
    (matrixCentralizerSplitEquiv_scalarRange A b htwo hsquare) B]
  simp only [MulEquiv.symm_apply_apply, ordinaryCentralizerScalarQuotientEquiv,
    MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem projectiveSplitQuotientEquiv_projection (A : Matrix.GeneralLinearGroup ι K) (b : Kˣ)
    (htwo : (2 : K) ≠ 0)
    (hsquare : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι (b ^ 2))
    (B : Subgroup.centralizer {A}) :
    projectiveSplitQuotientEquiv A b htwo hsquare
        ⟨ordinaryCentralizerProjection A B, ⟨B, rfl⟩⟩ =
      QuotientGroup.mk (matrixCentralizerSplitEquiv A b htwo hsquare B) := by
  apply (projectiveSplitQuotientEquiv A b htwo hsquare).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  exact (projectiveSplitQuotientEquiv_symm_mk A b htwo hsquare B).symm

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
