module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareSquareCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareNegative

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

open CatalogueBProjectiveInvolution

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem original_similarity_ratio_sign [Nontrivial V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ : K) (hd : d ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y) :
    μ / d = 1 ∨ μ / d = -1 :=
  multiplier_ratio_sign Q.polarBilin (_root_.LinearMap.BilinForm.Nondegenerate.ne_zero hQ)
    A d μ hd hsquare hsim

theorem negative_square_adjoint (Q : QuadraticForm K V) (A : V ≃ₗ[K] V)
    (d μ : K) (hd : d ≠ 0) (hsquare : ∀ x : V, A (A x) = d • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hnegative : μ / d = -1) (x y : V) :
    Q.polarBilin (A.toLinearMap x) y = -Q.polarBilin x (A.toLinearMap y) := by
  simpa only [hnegative, neg_one_mul, LinearEquiv.coe_toLinearMap] using
    scalar_square_adjoint Q.polarBilin A d μ hd hsquare hsim x y

theorem square_kernels_isCompl (A : V ≃ₗ[K] V) (d b : K)
    (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2) :
    IsCompl (positiveSquareKernel A b) (negativeSquareKernel A b) := by
  rw [positiveSquareKernel_eq A b hb, negativeSquareKernel_eq A b hb]
  exact squareScalar_eigenspaces_isCompl A.toLinearMap b hb h2
    (square_endomorphism_relation A d b hsquare hroot)

theorem positive_square_kernels_perpendicular (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (d μ b : K) (hd : d ≠ 0) (hb : b ≠ 0)
    (h2 : (2 : K) ≠ 0) (hsquare : ∀ x : V, A (A x) = d • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hpositive : μ / d = 1) :
    ∀ x ∈ positiveSquareKernel A b, ∀ y ∈ negativeSquareKernel A b,
      Q.polarBilin x y = 0 := by
  rw [positiveSquareKernel_eq A b hb, negativeSquareKernel_eq A b hb]
  intro x hx y hy
  exact opposite_eigenspaces_orthogonal Q.polarBilin A.toLinearMap b hb h2
    (positive_square_adjoint Q A d μ hd hsquare hsim hpositive) x y hx hy

variable [FiniteDimensional K V]

@[expose] def negativeSquareKernelCentralizerEquiv (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ b : K)
    (hd : d ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hnegative : μ / d = -1) :
    orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      (positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b) := by
  rw [positiveSquareKernel_eq A b hb]
  exact CatalogueBOrthogonalScalarSquareNegative.negativeCentralizerEquiv
    Q hQ A.toLinearMap b hb h2 (square_endomorphism_relation A d b hsquare hroot)
    (negative_square_adjoint Q A d μ hd hsquare hsim hnegative)

theorem negative_square_kernel_geometry (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ b : K)
    (hd : d ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hnegative : μ / d = -1) :
    (∀ x ∈ positiveSquareKernel A b, Q x = 0) ∧
      (∀ x ∈ negativeSquareKernel A b, Q x = 0) ∧
      (crossPairing Q.polarBilin (positiveSquareKernel A b)
        (negativeSquareKernel A b)).IsPerfPair ∧
      Module.finrank K (positiveSquareKernel A b) =
        Module.finrank K (negativeSquareKernel A b) ∧
      Module.finrank K (positiveSquareKernel A b) = Module.finrank K V / 2 ∧
      Module.finrank K (negativeSquareKernel A b) = Module.finrank K V / 2 := by
  rw [positiveSquareKernel_eq A b hb, negativeSquareKernel_eq A b hb]
  have h := CatalogueBOrthogonalScalarSquareNegative.negative_square_centralizer_structure
    Q hQ A.toLinearMap b hb h2 (square_endomorphism_relation A d b hsquare hroot)
    (negative_square_adjoint Q A d μ hd hsquare hsim hnegative)
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1⟩

theorem original_square_centralizer_structure [Nontrivial V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ b : K)
    (hd : d ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    (μ / d = 1 ∨ μ / d = -1) ∧
      IsCompl (positiveSquareKernel A b) (negativeSquareKernel A b) ∧
      positiveSquareKernel A b ≠ ⊥ ∧ negativeSquareKernel A b ≠ ⊥ ∧
      (μ / d = 1 →
        (∀ x ∈ positiveSquareKernel A b, ∀ y ∈ negativeSquareKernel A b,
          Q.polarBilin x y = 0) ∧
        (_root_.LinearMap.BilinForm.restrict Q.polarBilin
          (positiveSquareKernel A b)).Nondegenerate ∧
        (_root_.LinearMap.BilinForm.restrict Q.polarBilin
          (negativeSquareKernel A b)).Nondegenerate ∧
        Nonempty (orthogonalOperatorCentralizer Q A.toLinearMap ≃*
          (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (positiveSquareKernel A b).subtype) ×
            TauCeti.QuadraticMap.orthogonalGroup
              (Q.comp (negativeSquareKernel A b).subtype)))) ∧
      (μ / d = -1 →
        (∀ x ∈ positiveSquareKernel A b, Q x = 0) ∧
        (∀ x ∈ negativeSquareKernel A b, Q x = 0) ∧
        (crossPairing Q.polarBilin (positiveSquareKernel A b)
          (negativeSquareKernel A b)).IsPerfPair ∧
        Module.finrank K (positiveSquareKernel A b) =
          Module.finrank K (negativeSquareKernel A b) ∧
        Module.finrank K (positiveSquareKernel A b) = Module.finrank K V / 2 ∧
        Module.finrank K (negativeSquareKernel A b) = Module.finrank K V / 2 ∧
        Nonempty (orthogonalOperatorCentralizer Q A.toLinearMap ≃*
          (positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b))) := by
  have hn := square_kernels_ne_bot A d b hb h2 hsquare hroot hnonscalar
  refine ⟨original_similarity_ratio_sign Q hQ A d μ hd hsquare hsim,
    square_kernels_isCompl A d b hb h2 hsquare hroot, hn.1, hn.2, ?_, ?_⟩
  · intro hp
    have hnd := positive_square_kernel_nondegenerate Q hQ A d μ b hd hb h2
      hsquare hroot hsim hp
    exact ⟨positive_square_kernels_perpendicular Q A d μ b hd hb h2 hsquare hsim hp,
      hnd.1, hnd.2,
      ⟨positiveSquareKernelCentralizerEquiv Q A d μ b hd hb h2 hsquare hroot hsim hp⟩⟩
  · intro hm
    have h := negative_square_kernel_geometry Q hQ A d μ b hd hb h2 hsquare hroot hsim hm
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2,
      ⟨negativeSquareKernelCentralizerEquiv Q hQ A d μ b hd hb h2 hsquare hroot hsim hm⟩⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
