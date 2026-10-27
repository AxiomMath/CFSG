module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsPositive

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

open CatalogueBOrthogonalScalarSquareField CatalogueBOrthogonalScalarSquare
  CatalogueBProjectiveInvolution

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Nontrivial V]

section Positive

variable (Q : QuadraticForm K V) (T : Module.End K V) (d : K) (hd : d ≠ 0)
  (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
  (hadj : ∀ x y, Q.polarBilin (T x) y = Q.polarBilin x (T y)) (h2 : (2 : K) ≠ 0)

@[expose] def positiveCentralizerToOrthogonal (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    orthogonalOperatorCentralizer Q T →*
      TauCeti.QuadraticMap.orthogonalGroup (actualPositiveQuadratic Q T d hd hns hsquare hadj) := by
  letI := scalarField T d hns hsquare
  letI := evaluationModule T
  refine { toFun := ?_, map_one' := ?_, map_mul' := ?_ }
  · intro g
    refine ⟨centralizerEvaluationEquiv T (orthogonalCentralizerToOperator Q T g), ?_⟩
    apply (quadraticOfPolar_isometry_iff _
      (actualPositiveBilinear_isSymm Q T d hd hns hsquare hadj)
      (extension_two_ne_zero h2) _).mpr
    change ∀ x y, positiveFormula Q.polarBilin T d (generator T) (g.val.val x) (g.val.val y) =
      positiveFormula Q.polarBilin T d (generator T) x y
    apply (positiveFormula_isometry_iff Q.polarBilin T d (generator T)
      (scalarBasis T d hns hsquare) (scalarBasis_zero T d hns hsquare)
      (scalarBasis_one T d hns hsquare) g.val.val g.property).mpr
    exact (originalQuadratic_isometry_iff Q h2 g.val.val).mp g.val.property
  · ext x
    rfl
  · intro g g'
    ext x
    rfl

@[expose] def positiveOrthogonalToCentralizer (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    TauCeti.QuadraticMap.orthogonalGroup
        (actualPositiveQuadratic Q T d hd hns hsquare hadj) → orthogonalOperatorCentralizer Q T := by
  letI := scalarField T d hns hsquare
  letI := evaluationModule T
  intro g
  let gK := evaluationToCentralizer T g.val
  refine ⟨⟨gK.val, ?_⟩, gK.property⟩
  apply (originalQuadratic_isometry_iff Q h2 gK.val).mpr
  apply (positiveFormula_isometry_iff Q.polarBilin T d (generator T)
    (scalarBasis T d hns hsquare) (scalarBasis_zero T d hns hsquare)
    (scalarBasis_one T d hns hsquare) gK.val gK.property).mp
  exact (quadraticOfPolar_isometry_iff _
    (actualPositiveBilinear_isSymm Q T d hd hns hsquare hadj)
    (extension_two_ne_zero h2) g.val).mp g.property

theorem positiveCentralizerToOrthogonal_apply (g : orthogonalOperatorCentralizer Q T) (x : V) :
    (positiveCentralizerToOrthogonal Q T d hd hns hsquare hadj h2 g).val x = g.val.val x := rfl

theorem positiveCentralizerToOrthogonal_symm_apply (g : orthogonalOperatorCentralizer Q T)
    (x : V) :
    (positiveCentralizerToOrthogonal Q T d hd hns hsquare hadj h2 g).val.symm x =
      g.val.val.symm x := rfl

theorem positiveOrthogonalToCentralizer_apply :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ (g : TauCeti.QuadraticMap.orthogonalGroup
      (actualPositiveQuadratic Q T d hd hns hsquare hadj)) (x : V),
      (positiveOrthogonalToCentralizer Q T d hd hns hsquare hadj h2 g).val.val x = g.val x := by
  intros
  rfl

theorem positiveOrthogonalToCentralizer_symm_apply :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ (g : TauCeti.QuadraticMap.orthogonalGroup
      (actualPositiveQuadratic Q T d hd hns hsquare hadj)) (x : V),
      (positiveOrthogonalToCentralizer Q T d hd hns hsquare hadj h2 g).val.val.symm x =
        g.val.symm x := by
  intros
  rfl

theorem positiveOrthogonalToCentralizer_upgrade (g : orthogonalOperatorCentralizer Q T) :
    positiveOrthogonalToCentralizer Q T d hd hns hsquare hadj h2
      (positiveCentralizerToOrthogonal Q T d hd hns hsquare hadj h2 g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  ext x
  rfl

theorem positiveCentralizerToOrthogonal_restriction :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ g : TauCeti.QuadraticMap.orthogonalGroup
      (actualPositiveQuadratic Q T d hd hns hsquare hadj),
      positiveCentralizerToOrthogonal Q T d hd hns hsquare hadj h2
        (positiveOrthogonalToCentralizer Q T d hd hns hsquare hadj h2 g) = g := by
  intro g
  apply Subtype.ext
  ext x
  rfl

@[expose] def actualPositiveCentralizerEquiv (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    orthogonalOperatorCentralizer Q T ≃*
      TauCeti.QuadraticMap.orthogonalGroup (actualPositiveQuadratic Q T d hd hns hsquare hadj) := by
  letI := scalarField T d hns hsquare
  letI := evaluationModule T
  exact {
    toFun := positiveCentralizerToOrthogonal Q T d hd hns hsquare hadj h2
    invFun := positiveOrthogonalToCentralizer Q T d hd hns hsquare hadj h2
    left_inv := positiveOrthogonalToCentralizer_upgrade Q T d hd hns hsquare hadj h2
    right_inv := positiveCentralizerToOrthogonal_restriction Q T d hd hns hsquare hadj h2
    map_mul' := (positiveCentralizerToOrthogonal Q T d hd hns hsquare hadj h2).map_mul }

theorem actualPositiveCentralizerEquiv_apply (g : orthogonalOperatorCentralizer Q T) (x : V) :
    (actualPositiveCentralizerEquiv Q T d hd hns hsquare hadj h2 g).val x = g.val.val x := rfl

theorem actualPositiveCentralizerEquiv_symm_apply :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ (g : TauCeti.QuadraticMap.orthogonalGroup
      (actualPositiveQuadratic Q T d hd hns hsquare hadj)) (x : V),
      ((actualPositiveCentralizerEquiv Q T d hd hns hsquare hadj h2).symm g).val.val x =
        g.val x := by
  intros
  rfl

end Positive

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
