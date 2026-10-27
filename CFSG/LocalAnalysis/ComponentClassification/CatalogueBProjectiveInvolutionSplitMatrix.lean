module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveCoordinatesBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveCoordinatesCentralizer
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

open CatalogueBProjectiveCoordinates

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

abbrev splitMatrixOperator (A : Matrix.GeneralLinearGroup ι K) : Module.End K (ι → K) :=
  (matrixActionEquiv A).toLinearMap

theorem splitMatrixOperator_square (A : Matrix.GeneralLinearGroup ι K) (b : Kˣ)
    (hsquare : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι (b ^ 2)) :
    splitMatrixOperator A * splitMatrixOperator A = b.val ^ 2 • (1 : Module.End K (ι → K)) := by
  have h := congrArg (fun B : Matrix.GeneralLinearGroup ι K => (matrixActionEquiv B).toLinearMap)
    hsquare
  rw [map_pow, matrixActionEquiv_scalar] at h
  exact h

@[expose] def positiveMatrixDimension (A : Matrix.GeneralLinearGroup ι K) (b : K) : ℕ :=
  Module.finrank K ((splitMatrixOperator A).eigenspace b)

@[expose] def negativeMatrixDimension (A : Matrix.GeneralLinearGroup ι K) (b : K) : ℕ :=
  Module.finrank K ((splitMatrixOperator A).eigenspace (-b))

theorem splitMatrixDimension_sum (A : Matrix.GeneralLinearGroup ι K) (b : Kˣ)
    (htwo : (2 : K) ≠ 0)
    (hsquare : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι (b ^ 2)) :
    positiveMatrixDimension A b.val + negativeMatrixDimension A b.val = Fintype.card ι := by
  simpa only [positiveMatrixDimension, negativeMatrixDimension, Module.finrank_pi] using
    squareScalar_eigenspace_finrank (splitMatrixOperator A) b.val b.ne_zero htwo
      (splitMatrixOperator_square A b hsquare)

theorem splitMatrixDimension_pos (A : Matrix.GeneralLinearGroup ι K) (b : Kˣ)
    (htwo : (2 : K) ≠ 0)
    (hsquare : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι (b ^ 2))
    (hnonscalar : ∀ c : K, splitMatrixOperator A ≠ c • (1 : Module.End K (ι → K))) :
    0 < positiveMatrixDimension A b.val ∧ 0 < negativeMatrixDimension A b.val :=
  squareScalar_eigenspace_finrank_pos (splitMatrixOperator A) b.val b.ne_zero htwo
    (splitMatrixOperator_square A b hsquare) hnonscalar

@[expose] def positiveMatrixBasis (A : Matrix.GeneralLinearGroup ι K) (b : K) :
    Module.Basis (Fin (positiveMatrixDimension A b)) K ((splitMatrixOperator A).eigenspace b) :=
  Module.finBasis K ((splitMatrixOperator A).eigenspace b)

@[expose] def negativeMatrixBasis (A : Matrix.GeneralLinearGroup ι K) (b : K) :
    Module.Basis (Fin (negativeMatrixDimension A b)) K ((splitMatrixOperator A).eigenspace (-b)) :=
  Module.finBasis K ((splitMatrixOperator A).eigenspace (-b))

@[expose] def eigenspaceMatrixEquiv (A : Matrix.GeneralLinearGroup ι K) (b : K) :
    (((splitMatrixOperator A).eigenspace b ≃ₗ[K] (splitMatrixOperator A).eigenspace b) ×
      ((splitMatrixOperator A).eigenspace (-b) ≃ₗ[K] (splitMatrixOperator A).eigenspace (-b))) ≃*
      (Matrix.GeneralLinearGroup (Fin (positiveMatrixDimension A b)) K ×
        Matrix.GeneralLinearGroup (Fin (negativeMatrixDimension A b)) K) :=
  MulEquiv.prodCongr (basisAutomorphismMatrixEquiv (positiveMatrixBasis A b))
    (basisAutomorphismMatrixEquiv (negativeMatrixBasis A b))

@[expose] def matrixCentralizerSplitEquiv (A : Matrix.GeneralLinearGroup ι K) (b : Kˣ)
    (htwo : (2 : K) ≠ 0)
    (hsquare : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι (b ^ 2)) :
    Subgroup.centralizer {A} ≃*
      (Matrix.GeneralLinearGroup (Fin (positiveMatrixDimension A b.val)) K ×
        Matrix.GeneralLinearGroup (Fin (negativeMatrixDimension A b.val)) K) :=
  ((matrixCentralizerEquiv A).trans
    (splitCentralizerEquiv (splitMatrixOperator A) b.val b.ne_zero htwo
      (splitMatrixOperator_square A b hsquare))).trans (eigenspaceMatrixEquiv A b.val)

theorem matrixCentralizerSplitEquiv_apply (A : Matrix.GeneralLinearGroup ι K) (b : Kˣ)
    (htwo : (2 : K) ≠ 0)
    (hsquare : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι (b ^ 2))
    (B : Subgroup.centralizer {A}) :
    matrixCentralizerSplitEquiv A b htwo hsquare B =
      (basisAutomorphismMatrixEquiv (positiveMatrixBasis A b.val)
          (operatorCentralizerRestriction (splitMatrixOperator A) b.val (matrixCentralizerEquiv A B)),
        basisAutomorphismMatrixEquiv (negativeMatrixBasis A b.val)
          (operatorCentralizerRestriction (splitMatrixOperator A) (-b.val) (matrixCentralizerEquiv A B))) :=
  rfl

theorem matrixCentralizerSplitEquiv_scalar (A : Matrix.GeneralLinearGroup ι K) (b : Kˣ)
    (htwo : (2 : K) ≠ 0)
    (hsquare : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι (b ^ 2)) (c : Kˣ) :
    matrixCentralizerSplitEquiv A b htwo hsquare (ordinaryCentralizerScalar A c) =
      (Matrix.GeneralLinearGroup.scalar (Fin (positiveMatrixDimension A b.val)) c,
        Matrix.GeneralLinearGroup.scalar (Fin (negativeMatrixDimension A b.val)) c) := by
  change eigenspaceMatrixEquiv A b.val
    (splitCentralizerEquiv (splitMatrixOperator A) b.val b.ne_zero htwo
      (splitMatrixOperator_square A b hsquare)
        (matrixCentralizerEquiv A (ordinaryCentralizerScalar A c))) = _
  rw [matrixCentralizerEquiv_scalar, splitCentralizerEquiv_scalar]
  change (basisAutomorphismMatrixEquiv (positiveMatrixBasis A b.val) (LinearEquiv.smulOfUnit c),
    basisAutomorphismMatrixEquiv (negativeMatrixBasis A b.val) (LinearEquiv.smulOfUnit c)) = _
  rw [basisAutomorphismMatrixEquiv_scalar, basisAutomorphismMatrixEquiv_scalar]

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
