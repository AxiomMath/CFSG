module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsNegative
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometrySpaces

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

open CatalogueBOrthogonalScalarSquareField CatalogueBOrthogonalScalarSquare
  CatalogueBProjectiveInvolution

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Nontrivial V]

section Negative

variable (Q : QuadraticForm K V) (T : Module.End K V) (d : K) (hd : d ≠ 0)
  (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
  (hadj : ∀ x y, Q.polarBilin (T x) y = -Q.polarBilin x (T y)) (h2 : (2 : K) ≠ 0)

@[expose] def negativeCentralizerToUnitary (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    orthogonalOperatorCentralizer Q T →*
      CatalogueBUnitaryIsometry.isometryGroup
        (actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj) := by
  letI := scalarField T d hns hsquare
  letI := evaluationModule T
  refine { toFun := ?_, map_one' := ?_, map_mul' := ?_ }
  · intro g
    refine ⟨centralizerEvaluationEquiv T (orthogonalCentralizerToOperator Q T g), ?_⟩
    change ∀ x y, negativeFormula Q.polarBilin T d (generator T) (g.val.val x) (g.val.val y) =
      negativeFormula Q.polarBilin T d (generator T) x y
    apply (negativeFormula_isometry_iff Q.polarBilin T d (generator T)
      (scalarBasis T d hns hsquare) (scalarBasis_zero T d hns hsquare)
      (scalarBasis_one T d hns hsquare) g.val.val g.property).mpr
    exact (originalQuadratic_isometry_iff Q h2 g.val.val).mp g.val.property
  · ext x
    rfl
  · intro g g'
    ext x
    rfl

@[expose] def negativeUnitaryToCentralizer (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    CatalogueBUnitaryIsometry.isometryGroup
        (actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj) →
      orthogonalOperatorCentralizer Q T := by
  letI := scalarField T d hns hsquare
  letI := evaluationModule T
  intro g
  let gK := evaluationToCentralizer T g.val
  refine ⟨⟨gK.val, ?_⟩, gK.property⟩
  apply (originalQuadratic_isometry_iff Q h2 gK.val).mpr
  apply (negativeFormula_isometry_iff Q.polarBilin T d (generator T)
    (scalarBasis T d hns hsquare) (scalarBasis_zero T d hns hsquare)
    (scalarBasis_one T d hns hsquare) gK.val gK.property).mp
  exact g.property

theorem negativeCentralizerToUnitary_apply (g : orthogonalOperatorCentralizer Q T) (x : V) :
    (negativeCentralizerToUnitary Q T d hd hns hsquare hadj h2 g).val x = g.val.val x := rfl

theorem negativeCentralizerToUnitary_symm_apply (g : orthogonalOperatorCentralizer Q T)
    (x : V) :
    (negativeCentralizerToUnitary Q T d hd hns hsquare hadj h2 g).val.symm x =
      g.val.val.symm x := rfl

theorem negativeUnitaryToCentralizer_apply :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ (g : CatalogueBUnitaryIsometry.isometryGroup
      (actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj)) (x : V),
      (negativeUnitaryToCentralizer Q T d hd hns hsquare hadj h2 g).val.val x = g.val x := by
  intros
  rfl

theorem negativeUnitaryToCentralizer_symm_apply :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ (g : CatalogueBUnitaryIsometry.isometryGroup
      (actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj)) (x : V),
      (negativeUnitaryToCentralizer Q T d hd hns hsquare hadj h2 g).val.val.symm x =
        g.val.symm x := by
  intros
  rfl

theorem negativeUnitaryToCentralizer_upgrade (g : orthogonalOperatorCentralizer Q T) :
    negativeUnitaryToCentralizer Q T d hd hns hsquare hadj h2
      (negativeCentralizerToUnitary Q T d hd hns hsquare hadj h2 g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  ext x
  rfl

theorem negativeCentralizerToUnitary_restriction :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ g : CatalogueBUnitaryIsometry.isometryGroup
      (actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj),
      negativeCentralizerToUnitary Q T d hd hns hsquare hadj h2
        (negativeUnitaryToCentralizer Q T d hd hns hsquare hadj h2 g) = g := by
  intro g
  apply Subtype.ext
  ext x
  rfl

@[expose] def actualNegativeCentralizerEquiv (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    orthogonalOperatorCentralizer Q T ≃*
      CatalogueBUnitaryIsometry.isometryGroup
        (actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj) := by
  letI := scalarField T d hns hsquare
  letI := evaluationModule T
  exact {
    toFun := negativeCentralizerToUnitary Q T d hd hns hsquare hadj h2
    invFun := negativeUnitaryToCentralizer Q T d hd hns hsquare hadj h2
    left_inv := negativeUnitaryToCentralizer_upgrade Q T d hd hns hsquare hadj h2
    right_inv := negativeCentralizerToUnitary_restriction Q T d hd hns hsquare hadj h2
    map_mul' := (negativeCentralizerToUnitary Q T d hd hns hsquare hadj h2).map_mul }

theorem actualNegativeCentralizerEquiv_apply (g : orthogonalOperatorCentralizer Q T) (x : V) :
    (actualNegativeCentralizerEquiv Q T d hd hns hsquare hadj h2 g).val x = g.val.val x := rfl

theorem actualNegativeCentralizerEquiv_symm_apply :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ (g : CatalogueBUnitaryIsometry.isometryGroup
      (actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj)) (x : V),
      ((actualNegativeCentralizerEquiv Q T d hd hns hsquare hadj h2).symm g).val.val x =
        g.val x := by
  intros
  rfl

end Negative

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
