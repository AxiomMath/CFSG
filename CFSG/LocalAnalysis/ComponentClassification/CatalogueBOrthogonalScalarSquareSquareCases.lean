module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquarePositive
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareEigenspaces

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def positiveSquareKernel (A : V ≃ₗ[K] V) (b : K) : Submodule K V :=
  (b⁻¹ • A.toLinearMap - (1 : Module.End K V)).ker

@[expose] def negativeSquareKernel (A : V ≃ₗ[K] V) (b : K) : Submodule K V :=
  (b⁻¹ • A.toLinearMap + (1 : Module.End K V)).ker

theorem positiveSquareKernel_eq (A : V ≃ₗ[K] V) (b : K) (hb : b ≠ 0) :
    positiveSquareKernel A b = Module.End.eigenspace A.toLinearMap b := by
  ext x
  simp only [positiveSquareKernel, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero,
    Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    have hh := congrArg (fun y : V => b • y) h
    simpa only [smul_smul, mul_inv_cancel₀ hb, one_smul] using hh
  · intro h
    rw [h, smul_smul, inv_mul_cancel₀ hb, one_smul]

theorem negativeSquareKernel_eq (A : V ≃ₗ[K] V) (b : K) (hb : b ≠ 0) :
    negativeSquareKernel A b = Module.End.eigenspace A.toLinearMap (-b) := by
  ext x
  simp only [negativeSquareKernel, LinearMap.mem_ker, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg,
    Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    have hh := congrArg (fun y : V => b • y) h
    simpa only [smul_smul, mul_inv_cancel₀ hb, one_smul, smul_neg, neg_smul] using hh
  · intro h
    rw [h, smul_smul, mul_neg, inv_mul_cancel₀ hb, neg_one_smul]

theorem square_endomorphism_relation (A : V ≃ₗ[K] V) (d b : K)
    (hsquare : ∀ x : V, A (A x) = d • x) (hd : d = b ^ 2) :
    A.toLinearMap * A.toLinearMap = b ^ 2 • (1 : Module.End K V) := by
  ext x
  change A (A x) = b ^ 2 • x
  rw [hsquare, hd]

theorem positive_square_adjoint (Q : QuadraticForm K V) (A : V ≃ₗ[K] V)
    (d μ : K) (hd : d ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hpositive : μ / d = 1) (x y : V) :
    Q.polarBilin (A.toLinearMap x) y = Q.polarBilin x (A.toLinearMap y) := by
  simpa only [hpositive, one_mul, LinearEquiv.coe_toLinearMap] using
    scalar_square_adjoint Q.polarBilin A d μ hd hsquare hsim x y

theorem positive_square_kernel_nondegenerate (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ b : K)
    (hd : d ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hpositive : μ / d = 1) :
    (_root_.LinearMap.BilinForm.restrict Q.polarBilin (positiveSquareKernel A b)).Nondegenerate ∧
      (_root_.LinearMap.BilinForm.restrict Q.polarBilin (negativeSquareKernel A b)).Nondegenerate := by
  rw [positiveSquareKernel_eq A b hb, negativeSquareKernel_eq A b hb]
  exact positive_adjoint_eigenspaces_nondegenerate Q.polarBilin hQ
    ⟨fun x y => QuadraticMap.polar_comm Q x y⟩ A.toLinearMap b hb h2
    (square_endomorphism_relation A d b hsquare hroot)
    (positive_square_adjoint Q A d μ hd hsquare hsim hpositive)

@[expose] def positiveSquareKernelCentralizerEquiv (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (d μ b : K) (hd : d ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hpositive : μ / d = 1) :
    orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (positiveSquareKernel A b).subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp (negativeSquareKernel A b).subtype)) := by
  rw [positiveSquareKernel_eq A b hb, negativeSquareKernel_eq A b hb]
  exact positiveOrthogonalCentralizerEquiv Q A.toLinearMap b hb h2
    (square_endomorphism_relation A d b hsquare hroot)
    (positive_square_adjoint Q A d μ hd hsquare hsim hpositive)

theorem square_kernels_ne_bot (A : V ≃ₗ[K] V) (d b : K)
    (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    positiveSquareKernel A b ≠ ⊥ ∧ negativeSquareKernel A b ≠ ⊥ := by
  rw [positiveSquareKernel_eq A b hb, negativeSquareKernel_eq A b hb]
  exact CatalogueBProjectiveInvolution.squareScalar_eigenspaces_ne_bot
    A.toLinearMap b hb h2 (square_endomorphism_relation A d b hsquare hroot) hnonscalar

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
