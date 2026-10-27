module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructureSquare

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure

open CatalogueBOrthogonalScalarSquare

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem square_original_centralizer_structure (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ : K)
    (hd : d ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    ∀ b : Kˣ, d = (b : K) ^ 2 →
      IsCompl (positiveSquareKernel A b) (negativeSquareKernel A b) ∧
        positiveSquareKernel A b ≠ ⊥ ∧ negativeSquareKernel A b ≠ ⊥ ∧
        (μ / d = 1 →
          (∀ x ∈ positiveSquareKernel A b, ∀ y ∈ negativeSquareKernel A b,
            Q.polarBilin x y = 0) ∧
          (LinearMap.BilinForm.restrict Q.polarBilin (positiveSquareKernel A b)).Nondegenerate ∧
          (LinearMap.BilinForm.restrict Q.polarBilin (negativeSquareKernel A b)).Nondegenerate ∧
          ∃ e : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
            (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (positiveSquareKernel A b).subtype) ×
              TauCeti.QuadraticMap.orthogonalGroup (Q.comp (negativeSquareKernel A b).subtype)),
            (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) (x : positiveSquareKernel A b),
              (((e g).1).val x).val = g.val.val x.val) ∧
            (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) (y : negativeSquareKernel A b),
              (((e g).2).val y).val = g.val.val y.val) ∧
            (∀ g (x : positiveSquareKernel A b) (y : negativeSquareKernel A b),
              (e.symm g).val.val (x.val + y.val) = (g.1.val x).val + (g.2.val y).val)) ∧
        (μ / d = -1 →
          (∀ x ∈ positiveSquareKernel A b, Q x = 0) ∧
          (∀ y ∈ negativeSquareKernel A b, Q y = 0) ∧
          (crossPairing Q.polarBilin (positiveSquareKernel A b)
            (negativeSquareKernel A b)).IsPerfPair ∧
          Module.finrank K (positiveSquareKernel A b) =
            Module.finrank K (negativeSquareKernel A b) ∧
          Module.finrank K (positiveSquareKernel A b) = Module.finrank K V / 2 ∧
          Module.finrank K (negativeSquareKernel A b) = Module.finrank K V / 2 ∧
          ∃ (e : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
              (positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b))
            (dual : (positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b) →
              (negativeSquareKernel A b ≃ₗ[K] negativeSquareKernel A b)),
            (∀ f (x : positiveSquareKernel A b) (y : negativeSquareKernel A b),
              Q.polarBilin x.val (dual f y).val = Q.polarBilin (f.symm x).val y.val) ∧
            (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) (x : positiveSquareKernel A b),
              (e g x).val = g.val.val x.val) ∧
            (∀ f (x : positiveSquareKernel A b), (e.symm f).val.val x.val = (f x).val) ∧
            (∀ f (y : negativeSquareKernel A b), (e.symm f).val.val y.val = (dual f y).val)) := by
  intro b hroot
  have hb := Units.ne_zero b
  obtain ⟨hplus, hminus⟩ := square_kernels_ne_bot A d b hb h2 hsquare hroot hnonscalar
  refine ⟨square_kernels_isCompl A d b hb h2 hsquare hroot, hplus, hminus, ?_, ?_⟩
  · intro hp
    obtain ⟨hpnd, hmnd⟩ := positive_square_kernel_nondegenerate Q hQ A d μ b
      hd hb h2 hsquare hroot hsim hp
    exact ⟨positive_square_kernels_perpendicular Q A d μ b hd hb h2 hsquare hsim hp,
      hpnd, hmnd,
      positiveKernelCentralizerEquiv Q A d μ b hd hb h2 hsquare hroot hsim hp,
      positiveKernelCentralizerEquiv_positive Q A d μ b hd hb h2 hsquare hroot hsim hp,
      positiveKernelCentralizerEquiv_negative Q A d μ b hd hb h2 hsquare hroot hsim hp,
      positiveKernelCentralizerEquiv_symm_sum Q A d μ b hd hb h2 hsquare hroot hsim hp⟩
  · intro hm
    have h := negative_square_kernel_geometry Q hQ A d μ b hd hb h2 hsquare hroot hsim hm
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2,
      negativeKernelCentralizerEquiv Q hQ A d μ b hd hb h2 hsquare hroot hsim hm,
      kernelInverseDual Q hQ A d μ b hd hb h2 hsquare hroot hsim hm,
      kernelInverseDual_pairing Q hQ A d μ b hd hb h2 hsquare hroot hsim hm,
      negativeKernelCentralizerEquiv_apply Q hQ A d μ b hd hb h2 hsquare hroot hsim hm,
      negativeKernelCentralizerEquiv_symm_positive Q hQ A d μ b hd hb h2 hsquare hroot hsim hm,
      negativeKernelCentralizerEquiv_symm_negative Q hQ A d μ b hd hb h2 hsquare hroot hsim hm⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
