module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticMatrix

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

open CatalogueBProjectiveInvolution CatalogueBProjectiveCoordinates

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

@[expose] def matrixKScalars (lambda : K) (m : ℕ) :
    Kˣ →* Matrix.GeneralLinearGroup (Fin m) (extension lambda) :=
  (Matrix.GeneralLinearGroup.scalar (Fin m)).comp
    (Units.map (algebraMap K (extension lambda)).toMonoidHom)

theorem matrixKScalars_apply (lambda : K) (m : ℕ) (c : Kˣ) :
    matrixKScalars lambda m c = Matrix.GeneralLinearGroup.scalar (Fin m)
      (Units.map (algebraMap K (extension lambda)).toMonoidHom c) := rfl

theorem mem_matrixKScalars_range (lambda : K) (m : ℕ)
    (B : Matrix.GeneralLinearGroup (Fin m) (extension lambda)) :
    B ∈ (matrixKScalars lambda m).range ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin m)
        (Units.map (algebraMap K (extension lambda)).toMonoidHom c) = B :=
  Iff.rfl

theorem matrixKScalars_range_le_center (lambda : K) (m : ℕ) :
    (matrixKScalars lambda m).range ≤
      Subgroup.center (Matrix.GeneralLinearGroup (Fin m) (extension lambda)) := by
  rintro B ⟨c, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro D
  exact (Matrix.GeneralLinearGroup.scalar_commute
    (Units.map (algebraMap K (extension lambda)).toMonoidHom c) D).symm

instance matrixKScalars_range_normal (lambda : K) (m : ℕ) :
    (matrixKScalars lambda m).range.Normal :=
  Subgroup.normal_of_le_center (matrixKScalars_range_le_center lambda m)

theorem matrixCentralizerQuadraticEquiv_scalarRange (A : Matrix.GeneralLinearGroup ι K)
    (lambda : Kˣ) [Fact (¬ IsSquare lambda.val)]
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) :
    (ordinaryCentralizerScalar A).range.map
        (matrixCentralizerQuadraticEquiv A lambda hsq).toMonoidHom =
      (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range :=
  scalarRange_map_of_compatible A (matrixCentralizerQuadraticEquiv A lambda hsq)
    (matrixKScalars lambda.val (matrixDimension A lambda hsq))
    (matrixCentralizerQuadraticEquiv_scalar A lambda hsq)

@[expose] def projectiveQuadraticQuotientEquiv (A : Matrix.GeneralLinearGroup ι K)
    (lambda : Kˣ) [Fact (¬ IsSquare lambda.val)]
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) :
    (ordinaryCentralizerProjection A).range ≃*
      (Matrix.GeneralLinearGroup (Fin (matrixDimension A lambda hsq)) (extension lambda.val) ⧸
        (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range) :=
  ordinaryCentralizerCoordinateQuotientEquiv A (matrixCentralizerQuadraticEquiv A lambda hsq)
    (matrixKScalars lambda.val (matrixDimension A lambda hsq))
    (matrixCentralizerQuadraticEquiv_scalar A lambda hsq)

theorem projectiveQuadraticQuotientEquiv_symm_mk (A : Matrix.GeneralLinearGroup ι K)
    (lambda : Kˣ) [Fact (¬ IsSquare lambda.val)]
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda)
    (B : Subgroup.centralizer {A}) :
    ((projectiveQuadraticQuotientEquiv A lambda hsq).symm
      (QuotientGroup.mk (matrixCentralizerQuadraticEquiv A lambda hsq B))).val =
      ordinaryCentralizerProjection A B := by
  change ((ordinaryCentralizerScalarQuotientEquiv A)
    ((QuotientGroup.congr (ordinaryCentralizerScalar A).range
      (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range
      (matrixCentralizerQuadraticEquiv A lambda hsq)
      (matrixCentralizerQuadraticEquiv_scalarRange A lambda hsq)).symm
        (QuotientGroup.mk (matrixCentralizerQuadraticEquiv A lambda hsq B)))).val = _
  rw [← QuotientGroup.congr_mk (ordinaryCentralizerScalar A).range
    (matrixKScalars lambda.val (matrixDimension A lambda hsq)).range
    (matrixCentralizerQuadraticEquiv A lambda hsq)
    (matrixCentralizerQuadraticEquiv_scalarRange A lambda hsq) B]
  simp only [MulEquiv.symm_apply_apply, ordinaryCentralizerScalarQuotientEquiv,
    MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem projectiveQuadraticQuotientEquiv_projection (A : Matrix.GeneralLinearGroup ι K)
    (lambda : Kˣ) [Fact (¬ IsSquare lambda.val)]
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda)
    (B : Subgroup.centralizer {A}) :
    projectiveQuadraticQuotientEquiv A lambda hsq
        ⟨ordinaryCentralizerProjection A B, ⟨B, rfl⟩⟩ =
      QuotientGroup.mk (matrixCentralizerQuadraticEquiv A lambda hsq B) := by
  apply (projectiveQuadraticQuotientEquiv A lambda hsq).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  exact (projectiveQuadraticQuotientEquiv_symm_mk A lambda hsq B).symm

end CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
