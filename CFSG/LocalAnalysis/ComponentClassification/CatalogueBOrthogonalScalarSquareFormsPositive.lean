module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsQuadratic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

open CatalogueBOrthogonalScalarSquareField CatalogueBOrthogonalScalarSquare
  CatalogueBProjectiveInvolution

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Nontrivial V]

theorem actualScalarExpansion (T : Module.End K V) (d : K) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) (z : scalarAlgebra T) :
    z = algebraMap K (scalarAlgebra T) ((scalarBasis T d hns hsquare).repr z 0) +
      algebraMap K (scalarAlgebra T) ((scalarBasis T d hns hsquare).repr z 1) * generator T := by
  let := scalarField T d hns hsquare
  exact coordinate_expansion (scalarBasis T d hns hsquare) (generator T)
    (scalarBasis_zero T d hns hsquare) (scalarBasis_one T d hns hsquare) z

@[expose] def actualPositiveBilinear (B : LinearMap.BilinForm K V)
    (T : Module.End K V) (d : K) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (hadj : ∀ x y, B (T x) y = B x (T y)) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    LinearMap.BilinForm (scalarAlgebra T) V := by
  letI := scalarField T d hns hsquare
  letI := evaluationModule T
  letI := evaluationScalarTower T
  exact positiveBilinear B T d (generator T) hd (generator_square T d hsquare)
    (operator_square_apply T d hsquare) (evaluation_generator_smul T)
    (fun z => ⟨(scalarBasis T d hns hsquare).repr z 0,
      (scalarBasis T d hns hsquare).repr z 1, actualScalarExpansion T d hns hsquare z⟩) hadj

section Positive

variable (Q : QuadraticForm K V) (T : Module.End K V) (d : K) (hd : d ≠ 0)
  (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
  (hadj : ∀ x y, Q.polarBilin (T x) y = Q.polarBilin x (T y))

theorem actualPositiveBilinear_formula (x y : V) :
    actualPositiveBilinear Q.polarBilin T d hd hns hsquare hadj x y =
      algebraMap K (scalarAlgebra T) (Q.polarBilin x y) +
        algebraMap K (scalarAlgebra T) (d⁻¹ * Q.polarBilin (T x) y) * generator T := rfl

theorem actualPositiveBilinear_isSymm :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    (actualPositiveBilinear Q.polarBilin T d hd hns hsquare hadj).IsSymm := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  exact ⟨fun x y => (positiveFormula_symm Q.polarBilin T d (generator T)
    (LinearMap.BilinForm.isSymm_iff.mpr (originalPolar_isSymm Q)) hadj x y).symm⟩

theorem actualPositiveBilinear_nondegenerate (hQ : Q.polarBilin.Nondegenerate) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    (actualPositiveBilinear Q.polarBilin T d hd hns hsquare hadj).Nondegenerate := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  let := evaluationScalarTower T
  exact positiveBilinear_nondegenerate Q.polarBilin T d (generator T) hd
    (generator_square T d hsquare) (operator_square_apply T d hsquare)
    (evaluation_generator_smul T)
    (fun z => ⟨(scalarBasis T d hns hsquare).repr z 0,
      (scalarBasis T d hns hsquare).repr z 1, actualScalarExpansion T d hns hsquare z⟩)
    hadj (scalarBasis T d hns hsquare) (scalarBasis_zero T d hns hsquare)
    (scalarBasis_one T d hns hsquare) hQ

@[expose] def actualPositiveQuadratic :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    QuadraticForm (scalarAlgebra T) V := by
  letI := scalarField T d hns hsquare
  letI := evaluationModule T
  exact quadraticOfPolar (actualPositiveBilinear Q.polarBilin T d hd hns hsquare hadj)

theorem actualPositiveQuadratic_formula (x : V) :
    letI := scalarField T d hns hsquare
    actualPositiveQuadratic Q T d hd hns hsquare hadj x =
      (algebraMap K (scalarAlgebra T) (Q.polarBilin x x) +
        algebraMap K (scalarAlgebra T) (d⁻¹ * Q.polarBilin (T x) x) * generator T) / 2 := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  exact quadraticOfPolar_apply _ x

theorem actualPositiveQuadratic_polarBilin (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    (actualPositiveQuadratic Q T d hd hns hsquare hadj).polarBilin =
      actualPositiveBilinear Q.polarBilin T d hd hns hsquare hadj := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  exact quadraticOfPolar_polarBilin _
    (actualPositiveBilinear_isSymm Q T d hd hns hsquare hadj) (extension_two_ne_zero h2)

theorem actualPositiveQuadratic_nondegenerate (hQ : Q.polarBilin.Nondegenerate)
    (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    (actualPositiveQuadratic Q T d hd hns hsquare hadj).polarBilin.Nondegenerate := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  rw [actualPositiveQuadratic_polarBilin Q T d hd hns hsquare hadj h2]
  exact actualPositiveBilinear_nondegenerate Q T d hd hns hsquare hadj hQ

end Positive

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
