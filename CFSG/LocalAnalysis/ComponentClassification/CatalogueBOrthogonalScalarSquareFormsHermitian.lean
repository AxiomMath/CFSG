module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsPositive
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

open CatalogueBOrthogonalScalarSquareField

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Nontrivial V]

@[expose] def hermitianWithConjugation (B : LinearMap.BilinForm K V)
    (T : Module.End K V) (d : K) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (bar : scalarAlgebra T ≃ₐ[K] scalarAlgebra T) (hbar : bar (generator T) = -generator T)
    (hadj : ∀ x y, B (T x) y = -B x (T y)) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    V →ₛₗ[bar.toRingEquiv.toRingHom] V →ₗ[scalarAlgebra T] scalarAlgebra T := by
  letI := scalarField T d hns hsquare
  letI := evaluationModule T
  letI := evaluationScalarTower T
  exact negativeSesquilinear B T d (generator T) hd (generator_square T d hsquare)
    (operator_square_apply T d hsquare) (evaluation_generator_smul T)
    (fun z => ⟨(scalarBasis T d hns hsquare).repr z 0,
      (scalarBasis T d hns hsquare).repr z 1, actualScalarExpansion T d hns hsquare z⟩)
    bar hbar hadj

section Hermitian

variable (Q : QuadraticForm K V) (T : Module.End K V) (d : K) (hd : d ≠ 0)
  (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
  (bar : scalarAlgebra T ≃ₐ[K] scalarAlgebra T) (hbar : bar (generator T) = -generator T)
  (hadj : ∀ x y, Q.polarBilin (T x) y = -Q.polarBilin x (T y))

theorem hermitianWithConjugation_formula (x y : V) :
    hermitianWithConjugation Q.polarBilin T d hd hns hsquare bar hbar hadj x y =
      algebraMap K (scalarAlgebra T) (Q.polarBilin x y) +
        algebraMap K (scalarAlgebra T) (d⁻¹ * Q.polarBilin x (T y)) * generator T := rfl

theorem hermitianWithConjugation_isSymm :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    (hermitianWithConjugation Q.polarBilin T d hd hns hsquare bar hbar hadj).IsSymm := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  refine ⟨fun x y => ?_⟩
  change bar (negativeFormula Q.polarBilin T d (generator T) x y) =
    negativeFormula Q.polarBilin T d (generator T) y x
  exact (negativeFormula_hermitian Q.polarBilin T d (generator T) bar hbar
    (LinearMap.BilinForm.isSymm_iff.mpr (originalPolar_isSymm Q)) hadj x y).symm

theorem hermitianWithConjugation_nondegenerate (hQ : Q.polarBilin.Nondegenerate) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    (hermitianWithConjugation Q.polarBilin T d hd hns hsquare bar hbar hadj).Nondegenerate := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  let := evaluationScalarTower T
  exact negativeSesquilinear_nondegenerate Q.polarBilin T d (generator T) hd
    (generator_square T d hsquare) (operator_square_apply T d hsquare)
    (evaluation_generator_smul T)
    (fun z => ⟨(scalarBasis T d hns hsquare).repr z 0,
      (scalarBasis T d hns hsquare).repr z 1, actualScalarExpansion T d hns hsquare z⟩)
    bar hbar hadj (scalarBasis T d hns hsquare) (scalarBasis_zero T d hns hsquare)
    (scalarBasis_one T d hns hsquare) hQ

theorem hermitianWithConjugation_swap (x y : V) :
    hermitianWithConjugation Q.polarBilin T d hd hns hsquare bar hbar hadj y x =
      bar (hermitianWithConjugation Q.polarBilin T d hd hns hsquare bar hbar hadj x y) := by
  let := scalarField T d hns hsquare
  exact negativeFormula_hermitian Q.polarBilin T d (generator T) bar hbar
    (LinearMap.BilinForm.isSymm_iff.mpr (originalPolar_isSymm Q)) hadj x y

theorem hermitianWithConjugation_smul_left :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ (z : scalarAlgebra T) (x y : V),
      hermitianWithConjugation Q.polarBilin T d hd hns hsquare bar hbar hadj (z • x) y =
        bar z * hermitianWithConjugation Q.polarBilin T d hd hns hsquare bar hbar hadj x y := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  intro z x y
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  rfl

theorem hermitianWithConjugation_smul_right :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ (z : scalarAlgebra T) (x y : V),
      hermitianWithConjugation Q.polarBilin T d hd hns hsquare bar hbar hadj x (z • y) =
        z * hermitianWithConjugation Q.polarBilin T d hd hns hsquare bar hbar hadj x y := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  intro z x y
  exact (hermitianWithConjugation Q.polarBilin T d hd hns hsquare bar hbar hadj x).map_smul z y

end Hermitian

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
