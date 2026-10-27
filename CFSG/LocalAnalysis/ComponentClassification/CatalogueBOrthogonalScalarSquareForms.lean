module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsPositiveCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsNegativeCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

open CatalogueBOrthogonalScalarSquareField CatalogueBOrthogonalScalarSquare

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Nontrivial V]

theorem positive_nonsquare_centralizer_structure (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (T : Module.End K V) (d : K) (hd : d ≠ 0)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (h2 : (2 : K) ≠ 0) (hadj : ∀ x y, Q.polarBilin (T x) y = Q.polarBilin x (T y)) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    let BE := actualPositiveBilinear Q.polarBilin T d hd hns hsquare hadj
    let QE := actualPositiveQuadratic Q T d hd hns hsquare hadj
    BE.IsSymm ∧ BE.Nondegenerate ∧ QE.polarBilin = BE ∧ QE.polarBilin.Nondegenerate ∧
      (∀ x y, BE x y = algebraMap K (scalarAlgebra T) (Q.polarBilin x y) +
        algebraMap K (scalarAlgebra T) (d⁻¹ * Q.polarBilin (T x) y) * generator T) ∧
      (∀ x, QE x = BE x x / 2) ∧
      ∃ e : orthogonalOperatorCentralizer Q T ≃* TauCeti.QuadraticMap.orthogonalGroup QE,
        (∀ (g : orthogonalOperatorCentralizer Q T) x, (e g).val x = g.val.val x) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup QE) x, (e.symm g).val.val x = g.val x) ∧
        (∀ (g : orthogonalOperatorCentralizer Q T) x, (e g).val.symm x = g.val.val.symm x) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup QE) x,
          (e.symm g).val.val.symm x = g.val.symm x) := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  refine ⟨actualPositiveBilinear_isSymm Q T d hd hns hsquare hadj,
    actualPositiveBilinear_nondegenerate Q T d hd hns hsquare hadj hQ,
    actualPositiveQuadratic_polarBilin Q T d hd hns hsquare hadj h2,
    actualPositiveQuadratic_nondegenerate Q T d hd hns hsquare hadj hQ h2,
    actualPositiveBilinear_formula Q T d hd hns hsquare hadj, ?_,
    actualPositiveCentralizerEquiv Q T d hd hns hsquare hadj h2, ?_, ?_, ?_, ?_⟩
  · intro x
    exact quadraticOfPolar_apply _ x
  · intro g x
    rfl
  · intro g x
    rfl
  · intro g x
    rfl
  · intro g x
    rfl

theorem negative_nonsquare_centralizer_structure (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (T : Module.End K V) (d : K) (hd : d ≠ 0)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (h2 : (2 : K) ≠ 0) (hadj : ∀ x y, Q.polarBilin (T x) y = -Q.polarBilin x (T y)) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    let h := actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj
    let bar := conjugation T d hns hsquare
    h.IsSymm ∧ h.Nondegenerate ∧
      (∀ x y, h x y = algebraMap K (scalarAlgebra T) (Q.polarBilin x y) +
        algebraMap K (scalarAlgebra T) (d⁻¹ * Q.polarBilin x (T y)) * generator T) ∧
      (∀ (z : scalarAlgebra T) x y, h (z • x) y = bar z * h x y) ∧
      (∀ (z : scalarAlgebra T) x y, h x (z • y) = z * h x y) ∧
      (∀ x y, h y x = bar (h x y)) ∧
      ∃ e : orthogonalOperatorCentralizer Q T ≃* CatalogueBUnitaryIsometry.isometryGroup h,
        (∀ (g : orthogonalOperatorCentralizer Q T) x, (e g).val x = g.val.val x) ∧
        (∀ (g : CatalogueBUnitaryIsometry.isometryGroup h) x, (e.symm g).val.val x = g.val x) ∧
        (∀ (g : orthogonalOperatorCentralizer Q T) x, (e g).val.symm x = g.val.val.symm x) ∧
        (∀ (g : CatalogueBUnitaryIsometry.isometryGroup h) x,
          (e.symm g).val.val.symm x = g.val.symm x) := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  refine ⟨actualNegativeHermitian_isSymm Q T d hd hns hsquare hadj,
    actualNegativeHermitian_nondegenerate Q T d hd hns hsquare hadj hQ,
    actualNegativeHermitian_formula Q T d hd hns hsquare hadj,
    actualNegativeHermitian_smul_left Q T d hd hns hsquare hadj,
    actualNegativeHermitian_smul_right Q T d hd hns hsquare hadj,
    actualNegativeHermitian_swap Q T d hd hns hsquare hadj,
    actualNegativeCentralizerEquiv Q T d hd hns hsquare hadj h2, ?_, ?_, ?_, ?_⟩
  · intro g x
    rfl
  · intro g x
    rfl
  · intro g x
    rfl
  · intro g x
    rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
