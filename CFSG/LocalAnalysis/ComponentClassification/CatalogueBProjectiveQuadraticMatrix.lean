module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticCommutant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveCoordinatesCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveCoordinatesBasis
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

open CatalogueBProjectiveInvolution CatalogueBProjectiveCoordinates

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

abbrev matrixOperator (A : Matrix.GeneralLinearGroup ι K) : Module.End K (ι → K) :=
  (matrixActionEquiv A).toLinearMap

theorem matrixOperator_apply (A : Matrix.GeneralLinearGroup ι K) (v : ι → K) :
    matrixOperator A v = A.val.mulVec v := rfl

theorem matrixOperator_square (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) :
    matrixOperator A ^ 2 = algebraMap K (Module.End K (ι → K)) lambda.val := by
  have h := congrArg (fun B : Matrix.GeneralLinearGroup ι K => (matrixActionEquiv B).toLinearMap) hsq
  rw [map_pow, matrixActionEquiv_scalar] at h
  exact h

@[expose, instance_reducible] def matrixModule (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) :
    Module (extension lambda.val) (ι → K) :=
  actionModule (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq)

theorem matrixModule_root_smul (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) (v : ι → K) :
    letI := matrixModule A lambda hsq
    AdjoinRoot.root (quadraticPolynomial lambda.val) • v = A.val.mulVec v :=
  actionModule_root_smul (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq) v

theorem matrixModule_algebraMap_smul (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) (c : K) (v : ι → K) :
    letI := matrixModule A lambda hsq
    algebraMap K (extension lambda.val) c • v = c • v :=
  actionModule_algebraMap_smul (matrixOperator A) lambda.val
    (matrixOperator_square A lambda hsq) c v

theorem matrixModule_scalarTower (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) :
    letI := matrixModule A lambda hsq
    IsScalarTower K (extension lambda.val) (ι → K) :=
  actionScalarTower (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq)

theorem matrixModule_finite (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) :
    letI := matrixModule A lambda hsq
    Module.Finite (extension lambda.val) (ι → K) :=
  actionModule_finite (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq)

@[expose] def matrixDimension (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) : ℕ :=
  letI := matrixModule A lambda hsq
  Module.finrank (extension lambda.val) (ι → K)

theorem matrixDimension_twice (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    [Fact (¬ IsSquare lambda.val)]
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) :
    Fintype.card ι = 2 * matrixDimension A lambda hsq := by
  simpa only [Module.finrank_pi, matrixDimension, matrixModule] using
    actionModule_finrank (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq)

theorem matrixDimension_pos [Nonempty ι] (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    [Fact (¬ IsSquare lambda.val)]
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) :
    0 < matrixDimension A lambda hsq :=
  actionModule_finrank_pos (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq)

@[expose] def matrixBasis (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    [Fact (¬ IsSquare lambda.val)]
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) :
    letI := matrixModule A lambda hsq
    Module.Basis (Fin (matrixDimension A lambda hsq)) (extension lambda.val) (ι → K) := by
  letI := matrixModule A lambda hsq
  letI := matrixModule_finite A lambda hsq
  exact Module.finBasis (extension lambda.val) (ι → K)

@[expose] def matrixCentralizerQuadraticEquiv (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    [Fact (¬ IsSquare lambda.val)]
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) :
    Subgroup.centralizer {A} ≃*
      Matrix.GeneralLinearGroup (Fin (matrixDimension A lambda hsq)) (extension lambda.val) := by
  letI := matrixModule A lambda hsq
  exact ((matrixCentralizerEquiv A).trans
    (quadraticCentralizerEquiv (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq))).trans
      (basisAutomorphismMatrixEquiv (matrixBasis A lambda hsq))

theorem matrixCentralizerQuadraticEquiv_mulVec (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    [Fact (¬ IsSquare lambda.val)]
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda)
    (B : Subgroup.centralizer {A}) (v : ι → K) :
    letI := matrixModule A lambda hsq
    (matrixCentralizerQuadraticEquiv A lambda hsq B).val.mulVec
        ((matrixBasis A lambda hsq).equivFun v) =
      (matrixBasis A lambda hsq).equivFun (B.val.val.mulVec v) := by
  let := matrixModule A lambda hsq
  exact basisAutomorphismMatrixEquiv_mulVec (matrixBasis A lambda hsq)
    (quadraticCentralizerEquiv (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq)
      (matrixCentralizerEquiv A B)) v

theorem matrixCentralizerQuadraticEquiv_scalar (A : Matrix.GeneralLinearGroup ι K) (lambda : Kˣ)
    [Fact (¬ IsSquare lambda.val)]
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar ι lambda) (c : Kˣ) :
    matrixCentralizerQuadraticEquiv A lambda hsq (ordinaryCentralizerScalar A c) =
      Matrix.GeneralLinearGroup.scalar (Fin (matrixDimension A lambda hsq))
        (Units.map (algebraMap K (extension lambda.val)).toMonoidHom c) := by
  let := matrixModule A lambda hsq
  change basisAutomorphismMatrixEquiv (matrixBasis A lambda hsq)
      (quadraticCentralizerEquiv (matrixOperator A) lambda.val (matrixOperator_square A lambda hsq)
        (matrixCentralizerEquiv A (ordinaryCentralizerScalar A c))) = _
  rw [matrixCentralizerEquiv_scalar, quadraticCentralizerEquiv_scalar,
    basisAutomorphismMatrixEquiv_scalar]

end CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
