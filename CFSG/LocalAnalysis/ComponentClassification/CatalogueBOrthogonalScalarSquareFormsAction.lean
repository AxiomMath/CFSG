module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

open CatalogueBOrthogonalScalarSquareField CatalogueBProjectiveInvolution
  CatalogueBOrthogonalScalarSquare

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem operator_square_apply (T : Module.End K V) (d : K)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) (x : V) :
    T (T x) = d • x := by
  have h := congrArg (fun L : Module.End K V => L x) hsquare
  change (T ^ 2) x = d • x at h
  simpa only [pow_two, Module.End.mul_apply] using h

@[expose] def centralizerEvaluationEquiv (T : Module.End K V) (g : operatorCentralizer T) :
    letI := evaluationModule T
    V ≃ₗ[scalarAlgebra T] V := by
  letI := evaluationModule T
  have hcomm : Commute g.val.toLinearMap T :=
    LinearMap.ext g.property
  exact {
    toFun := g.val
    invFun := g.val.symm
    left_inv := g.val.symm_apply_apply
    right_inv := g.val.apply_symm_apply
    map_add' := g.val.map_add
    map_smul' := (commute_iff_evaluation_linear T g.val.toLinearMap).mp hcomm }

theorem centralizerEvaluationEquiv_apply (T : Module.End K V)
    (g : operatorCentralizer T) (x : V) : centralizerEvaluationEquiv T g x = g.val x := rfl

theorem centralizerEvaluationEquiv_symm_apply (T : Module.End K V)
    (g : operatorCentralizer T) (x : V) :
    (centralizerEvaluationEquiv T g).symm x = g.val.symm x := rfl

@[expose] def evaluationToCentralizer (T : Module.End K V) :
    letI := evaluationModule T
    (V ≃ₗ[scalarAlgebra T] V) → operatorCentralizer T := by
  letI := evaluationModule T
  letI := evaluationCompatibleSMul T
  intro g
  refine ⟨g.restrictScalars K, ?_⟩
  intro x
  change g (T x) = T (g x)
  simpa only [evaluation_generator_smul] using g.map_smul (generator T) x

theorem evaluationToCentralizer_apply (T : Module.End K V) :
    letI := evaluationModule T
    ∀ (g : V ≃ₗ[scalarAlgebra T] V) (x : V), (evaluationToCentralizer T g).val x = g x := by
  intros
  rfl

theorem evaluationToCentralizer_symm_apply (T : Module.End K V) :
    letI := evaluationModule T
    ∀ (g : V ≃ₗ[scalarAlgebra T] V) (x : V),
      (evaluationToCentralizer T g).val.symm x = g.symm x := by
  intros
  rfl

theorem evaluationToCentralizer_evaluation (T : Module.End K V)
    (g : operatorCentralizer T) :
    evaluationToCentralizer T (centralizerEvaluationEquiv T g) = g := by
  apply Subtype.ext
  ext x
  rfl

theorem centralizerEvaluationEquiv_restriction (T : Module.End K V) :
    letI := evaluationModule T
    ∀ g : V ≃ₗ[scalarAlgebra T] V,
      centralizerEvaluationEquiv T (evaluationToCentralizer T g) = g := by
  intro g
  ext x
  rfl

@[expose] def operatorCentralizerEvaluationEquiv (T : Module.End K V) :
    letI := evaluationModule T
    operatorCentralizer T ≃* (V ≃ₗ[scalarAlgebra T] V) := by
  letI := evaluationModule T
  exact {
    toFun := centralizerEvaluationEquiv T
    invFun := evaluationToCentralizer T
    left_inv := evaluationToCentralizer_evaluation T
    right_inv := centralizerEvaluationEquiv_restriction T
    map_mul' := fun _ _ => by ext x; rfl }

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
