module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsHermitian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldConjugation

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

open CatalogueBOrthogonalScalarSquareField

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Nontrivial V]

@[expose] def actualNegativeHermitian (B : LinearMap.BilinForm K V)
    (T : Module.End K V) (d : K) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (hadj : ∀ x y, B (T x) y = -B x (T y)) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    V →ₛₗ[(conjugation T d hns hsquare).toRingEquiv.toRingHom]
      V →ₗ[scalarAlgebra T] scalarAlgebra T :=
  hermitianWithConjugation B T d hd hns hsquare (conjugation T d hns hsquare)
    (conjugation_generator T d hns hsquare) hadj

section Negative

variable (Q : QuadraticForm K V) (T : Module.End K V) (d : K) (hd : d ≠ 0)
  (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
  (hadj : ∀ x y, Q.polarBilin (T x) y = -Q.polarBilin x (T y))

theorem actualNegativeHermitian_formula (x y : V) :
    actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj x y =
      algebraMap K (scalarAlgebra T) (Q.polarBilin x y) +
        algebraMap K (scalarAlgebra T) (d⁻¹ * Q.polarBilin x (T y)) * generator T := rfl

theorem actualNegativeHermitian_isSymm :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    (actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj).IsSymm :=
  hermitianWithConjugation_isSymm Q T d hd hns hsquare (conjugation T d hns hsquare)
    (conjugation_generator T d hns hsquare) hadj

theorem actualNegativeHermitian_nondegenerate (hQ : Q.polarBilin.Nondegenerate) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    (actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj).Nondegenerate :=
  hermitianWithConjugation_nondegenerate Q T d hd hns hsquare (conjugation T d hns hsquare)
    (conjugation_generator T d hns hsquare) hadj hQ

theorem actualNegativeHermitian_swap (x y : V) :
    actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj y x =
      conjugation T d hns hsquare
        (actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj x y) :=
  hermitianWithConjugation_swap Q T d hd hns hsquare (conjugation T d hns hsquare)
    (conjugation_generator T d hns hsquare) hadj x y

theorem actualNegativeHermitian_smul_left :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ (z : scalarAlgebra T) (x y : V),
      actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj (z • x) y =
        conjugation T d hns hsquare z *
          actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj x y :=
  hermitianWithConjugation_smul_left Q T d hd hns hsquare (conjugation T d hns hsquare)
    (conjugation_generator T d hns hsquare) hadj

theorem actualNegativeHermitian_smul_right :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ (z : scalarAlgebra T) (x y : V),
      actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj x (z • y) =
        z * actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj x y :=
  hermitianWithConjugation_smul_right Q T d hd hns hsquare (conjugation T d hns hsquare)
    (conjugation_generator T d hns hsquare) hadj

end Negative

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
