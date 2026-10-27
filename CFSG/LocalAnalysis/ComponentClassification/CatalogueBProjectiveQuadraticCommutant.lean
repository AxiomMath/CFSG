module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionCommutant

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

open CatalogueBProjectiveInvolution

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem commute_actionHom (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda)
    (L : Module.End K V) (hLT : Commute L T) (x : extension lambda) :
    Commute L (actionHom T lambda hsq x) := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute (R := K)
  · rw [← actionHom_range T lambda hsq]
    exact ⟨x, rfl⟩
  · intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hLT

theorem commute_iff_action_linear (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) (L : Module.End K V) :
    letI := actionModule T lambda hsq
    Commute L T ↔ ∀ (x : extension lambda) (v : V), L (x • v) = x • L v := by
  constructor
  · intro hLT x v
    exact congrArg (fun F : Module.End K V => F v) (commute_actionHom T lambda hsq L hLT x).eq
  · intro hL
    apply LinearMap.ext
    intro v
    change L (T v) = T (L v)
    simpa only [actionModule_root_smul] using hL (AdjoinRoot.root (quadraticPolynomial lambda)) v

@[expose] def commutingLinearMap (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda)
    (L : Module.End K V) (hLT : Commute L T) :
    letI := actionModule T lambda hsq
    Module.End (extension lambda) V := by
  letI := actionModule T lambda hsq
  exact {
    toFun := L
    map_add' := L.map_add
    map_smul' := (commute_iff_action_linear T lambda hsq L).mp hLT }

theorem commutingLinearMap_apply (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda)
    (L : Module.End K V) (hLT : Commute L T) (v : V) :
    commutingLinearMap T lambda hsq L hLT v = L v := rfl

theorem actionCompatibleSMul (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    letI := actionModule T lambda hsq
    LinearMap.CompatibleSMul V V K (extension lambda) := by
  let := actionModule T lambda hsq
  refine ⟨fun L c v => ?_⟩
  rw [← actionModule_algebraMap_smul T lambda hsq c v, L.map_smul,
    actionModule_algebraMap_smul]

theorem extensionLinearMap_commutes (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    letI := actionModule T lambda hsq
    letI := actionCompatibleSMul T lambda hsq
    ∀ L : Module.End (extension lambda) V, Commute (L.restrictScalars K) T := by
  let := actionModule T lambda hsq
  let := actionCompatibleSMul T lambda hsq
  intro L
  apply LinearMap.ext
  intro v
  change L (T v) = T (L v)
  rw [← actionModule_root_smul T lambda hsq v, L.map_smul, actionModule_root_smul]

@[expose] def commutingLinearEquiv (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda)
    (B : operatorCentralizer T) :
    letI := actionModule T lambda hsq
    V ≃ₗ[extension lambda] V := by
  letI := actionModule T lambda hsq
  exact {
    toFun := B.val, invFun := B.val.symm,
    left_inv := B.val.symm_apply_apply, right_inv := B.val.apply_symm_apply,
    map_add' := B.val.map_add,
    map_smul' := (commute_iff_action_linear T lambda hsq B.val.toLinearMap).mp
      (LinearMap.ext B.property) }

@[expose] def extensionLinearEquivCentralizer (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    letI := actionModule T lambda hsq
    (V ≃ₗ[extension lambda] V) → operatorCentralizer T := by
  letI := actionModule T lambda hsq
  letI := actionCompatibleSMul T lambda hsq
  intro B
  refine ⟨B.restrictScalars K, fun v => ?_⟩
  change B (T v) = T (B v)
  rw [← actionModule_root_smul T lambda hsq v, B.map_smul, actionModule_root_smul]

@[expose] def quadraticCentralizerEquiv (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    letI := actionModule T lambda hsq
    operatorCentralizer T ≃* (V ≃ₗ[extension lambda] V) := by
  letI := actionModule T lambda hsq
  exact {
    toFun := commutingLinearEquiv T lambda hsq,
    invFun := extensionLinearEquivCentralizer T lambda hsq,
    left_inv := fun B => by apply Subtype.ext; ext v; rfl,
    right_inv := fun B => by ext v; rfl,
    map_mul' := fun B C => by ext v; rfl }

theorem quadraticCentralizerEquiv_apply (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda)
    (B : operatorCentralizer T) (v : V) :
    quadraticCentralizerEquiv T lambda hsq B v = B.val v := rfl

theorem quadraticCentralizerEquiv_symm_apply (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    letI := actionModule T lambda hsq
    ∀ (B : V ≃ₗ[extension lambda] V) (v : V),
      ((quadraticCentralizerEquiv T lambda hsq).symm B).val v = B v := by
  intros
  rfl

theorem quadraticCentralizerEquiv_scalar (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) (c : Kˣ) :
    letI := actionModule T lambda hsq
    quadraticCentralizerEquiv T lambda hsq (operatorCentralizerScalar T c) =
      LinearEquiv.smulOfUnit (Units.map (algebraMap K (extension lambda)).toMonoidHom c) := by
  ext v
  exact (actionModule_algebraMap_smul T lambda hsq c.val v).symm

theorem actionModule_finite [Module.Finite K V] (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    letI := actionModule T lambda hsq
    Module.Finite (extension lambda) V := by
  let := actionModule T lambda hsq
  let := actionScalarTower T lambda hsq
  exact Module.Finite.of_restrictScalars_finite K (extension lambda) V

theorem actionModule_finrank (T : Module.End K V) (lambda : K)
    [Fact (¬ IsSquare lambda)]
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    letI := actionModule T lambda hsq
    Module.finrank K V = 2 * Module.finrank (extension lambda) V := by
  let := actionModule T lambda hsq
  let := actionScalarTower T lambda hsq
  simpa only [extension_finrank] using (Module.finrank_mul_finrank K (extension lambda) V).symm

theorem actionModule_finrank_pos [Module.Finite K V] [Nontrivial V]
    (T : Module.End K V) (lambda : K) [Fact (¬ IsSquare lambda)]
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    letI := actionModule T lambda hsq
    0 < Module.finrank (extension lambda) V := by
  let := actionModule T lambda hsq
  let := actionModule_finite T lambda hsq
  exact Module.finrank_pos

end CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
