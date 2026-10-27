module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructureTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareSquareStructure

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure

open CatalogueBOrthogonalScalarSquare CatalogueBProjectiveInvolution
  CatalogueBOrthogonalScalarSquareNegative

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Positive

variable (Q : QuadraticForm K V) (A : V ≃ₗ[K] V) (d μ b : K)
  (hd : d ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
  (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
  (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
  (hp : μ / d = 1)

@[expose] def positiveKernelCentralizerEquiv :
    orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (positiveSquareKernel A b).subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp (negativeSquareKernel A b).subtype)) :=
  (positiveOrthogonalCentralizerEquiv Q A.toLinearMap b hb h2
    (square_endomorphism_relation A d b hsquare hroot)
    (positive_square_adjoint Q A d μ hd hsquare hsim hp)).trans
      (MulEquiv.prodCongr
        (orthogonalSubmoduleCongr Q _ _ (positiveSquareKernel_eq A b hb).symm)
        (orthogonalSubmoduleCongr Q _ _ (negativeSquareKernel_eq A b hb).symm))

theorem positiveKernelCentralizerEquiv_positive
    (g : orthogonalOperatorCentralizer Q A.toLinearMap) (x : positiveSquareKernel A b) :
    (((positiveKernelCentralizerEquiv Q A d μ b hd hb h2 hsquare hroot hsim hp g).1).val x).val =
      g.val.val x.val := by
  change ((orthogonalSubmoduleCongr Q _ _ (positiveSquareKernel_eq A b hb).symm
    (orthogonalCentralizerRestriction Q A.toLinearMap b g)).val x).val = _
  rw [orthogonalSubmoduleCongr_apply, orthogonalCentralizerRestriction_apply,
    LinearEquiv.coe_ofEq_apply]

theorem positiveKernelCentralizerEquiv_negative
    (g : orthogonalOperatorCentralizer Q A.toLinearMap) (x : negativeSquareKernel A b) :
    (((positiveKernelCentralizerEquiv Q A d μ b hd hb h2 hsquare hroot hsim hp g).2).val x).val =
      g.val.val x.val := by
  change ((orthogonalSubmoduleCongr Q _ _ (negativeSquareKernel_eq A b hb).symm
    (orthogonalCentralizerRestriction Q A.toLinearMap (-b) g)).val x).val = _
  rw [orthogonalSubmoduleCongr_apply, orthogonalCentralizerRestriction_apply,
    LinearEquiv.coe_ofEq_apply]

theorem positiveKernelCentralizerEquiv_symm_sum
    (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (positiveSquareKernel A b).subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (negativeSquareKernel A b).subtype))
    (x : positiveSquareKernel A b) (y : negativeSquareKernel A b) :
    ((positiveKernelCentralizerEquiv Q A d μ b hd hb h2 hsquare hroot hsim hp).symm g).val.val
      (x.val + y.val) = (g.1.val x).val + (g.2.val y).val := by
  let x' := LinearEquiv.ofEq _ _ (positiveSquareKernel_eq A b hb) x
  let y' := LinearEquiv.ofEq _ _ (negativeSquareKernel_eq A b hb) y
  have hx : x'.val = x.val := LinearEquiv.coe_ofEq_apply _ x
  have hy : y'.val = y.val := LinearEquiv.coe_ofEq_apply _ y
  let g' := ((orthogonalSubmoduleCongr Q _ _ (positiveSquareKernel_eq A b hb).symm).symm g.1,
    (orthogonalSubmoduleCongr Q _ _ (negativeSquareKernel_eq A b hb).symm).symm g.2)
  have h := positiveOrthogonalExtension_apply Q A.toLinearMap b hb h2
    (square_endomorphism_relation A d b hsquare hroot)
    (positive_square_adjoint Q A d μ hd hsquare hsim hp) g' (x', y')
  change (positiveOrthogonalExtension Q A.toLinearMap b hb h2
    (square_endomorphism_relation A d b hsquare hroot)
    (positive_square_adjoint Q A d μ hd hsquare hsim hp) g').val.val
      (x.val + y.val) = _
  change (positiveOrthogonalExtension Q A.toLinearMap b hb h2
    (square_endomorphism_relation A d b hsquare hroot)
    (positive_square_adjoint Q A d μ hd hsquare hsim hp) g').val.val
      (x'.val + y'.val) = (g'.1.val x').val + (g'.2.val y').val at h
  rw [hx, hy] at h
  rw [h]
  congr 1
  · dsimp only [g', x']
    rw [orthogonalSubmoduleCongr_symm_apply]
    apply congrArg (fun z => (g.1.val z).val)
    apply Subtype.ext
    simp only [LinearEquiv.coe_ofEq_apply]
  · dsimp only [g', y']
    rw [orthogonalSubmoduleCongr_symm_apply]
    apply congrArg (fun z => (g.2.val z).val)
    apply Subtype.ext
    simp only [LinearEquiv.coe_ofEq_apply]

end Positive

section Negative

variable [FiniteDimensional K V]
variable (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
  (A : V ≃ₗ[K] V) (d μ b : K)
  (hd : d ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
  (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
  (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
  (hm : μ / d = -1)

@[expose] def negativeKernelCentralizerEquiv :
    orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      (positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b) :=
  (negativeCentralizerEquiv Q hQ A.toLinearMap b hb h2
    (square_endomorphism_relation A d b hsquare hroot)
    (negative_square_adjoint Q A d μ hd hsquare hsim hm)).trans
      (linearSubmoduleCongr _ _ (positiveSquareKernel_eq A b hb).symm)

theorem negativeKernelCentralizerEquiv_apply
    (g : orthogonalOperatorCentralizer Q A.toLinearMap) (x : positiveSquareKernel A b) :
    (negativeKernelCentralizerEquiv Q hQ A d μ b hd hb h2 hsquare hroot hsim hm g x).val =
      g.val.val x.val := by
  change (linearSubmoduleCongr _ _ (positiveSquareKernel_eq A b hb).symm
    (negativeCentralizerRestriction Q A.toLinearMap b g) x).val = _
  rw [linearSubmoduleCongr_apply, negativeCentralizerRestriction_apply,
    LinearEquiv.coe_ofEq_apply]

theorem negativeKernelCentralizerEquiv_symm_positive
    (f : positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b)
    (x : positiveSquareKernel A b) :
    ((negativeKernelCentralizerEquiv Q hQ A d μ b hd hb h2 hsquare hroot hsim hm).symm f).val.val
      x.val = (f x).val := by
  let x' := LinearEquiv.ofEq _ _ (positiveSquareKernel_eq A b hb) x
  have hx : x'.val = x.val := LinearEquiv.coe_ofEq_apply _ x
  let f' := (linearSubmoduleCongr _ _ (positiveSquareKernel_eq A b hb).symm).symm f
  have h := negativeCentralizerEquiv_symm_positive Q hQ A.toLinearMap b hb h2
    (square_endomorphism_relation A d b hsquare hroot)
    (negative_square_adjoint Q A d μ hd hsquare hsim hm) f' x'
  change ((negativeCentralizerEquiv Q hQ A.toLinearMap b hb h2
    (square_endomorphism_relation A d b hsquare hroot)
    (negative_square_adjoint Q A d μ hd hsquare hsim hm)).symm f').val.val x.val = _
  rw [hx] at h
  rw [h]
  dsimp only [f', x']
  rw [linearSubmoduleCongr_symm_apply]
  apply congrArg (fun z => (f z).val)
  apply Subtype.ext
  simp only [LinearEquiv.coe_ofEq_apply]

@[expose] def kernelInverseDual
    (f : positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b) :
    negativeSquareKernel A b ≃ₗ[K] negativeSquareKernel A b := by
  letI := (negative_square_kernel_geometry Q hQ A d μ b hd hb h2
    hsquare hroot hsim hm).2.2.1
  exact inverseDualAction (crossPairing Q.polarBilin
    (positiveSquareKernel A b) (negativeSquareKernel A b)) f

theorem kernelInverseDual_pairing
    (f : positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b)
    (x : positiveSquareKernel A b) (y : negativeSquareKernel A b) :
    Q.polarBilin x.val (kernelInverseDual Q hQ A d μ b hd hb h2 hsquare hroot hsim hm f y).val =
      Q.polarBilin (f.symm x).val y.val := by
  let := (negative_square_kernel_geometry Q hQ A d μ b hd hb h2
    hsquare hroot hsim hm).2.2.1
  exact inverseDualAction_pairing (crossPairing Q.polarBilin
    (positiveSquareKernel A b) (negativeSquareKernel A b)) f x y

@[expose] def negativeKernelRestriction (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (b : K) (hb : b ≠ 0) :
    orthogonalOperatorCentralizer Q A.toLinearMap →*
      (negativeSquareKernel A b ≃ₗ[K] negativeSquareKernel A b) :=
  (linearSubmoduleCongr _ _ (negativeSquareKernel_eq A b hb).symm).toMonoidHom.comp
    (negativeCentralizerRestriction Q A.toLinearMap (-b))

omit [FiniteDimensional K V] in
theorem negativeKernelRestriction_apply (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (b : K) (hb : b ≠ 0)
    (g : orthogonalOperatorCentralizer Q A.toLinearMap) (y : negativeSquareKernel A b) :
    (negativeKernelRestriction Q A b hb g y).val = g.val.val y.val := by
  change (linearSubmoduleCongr _ _ (negativeSquareKernel_eq A b hb).symm
    (negativeCentralizerRestriction Q A.toLinearMap (-b) g) y).val = _
  rw [linearSubmoduleCongr_apply, negativeCentralizerRestriction_apply,
    LinearEquiv.coe_ofEq_apply]

theorem negativeKernelCentralizerEquiv_symm_negative
    (f : positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b)
    (y : negativeSquareKernel A b) :
    ((negativeKernelCentralizerEquiv Q hQ A d μ b hd hb h2 hsquare hroot hsim hm).symm f).val.val
      y.val = (kernelInverseDual Q hQ A d μ b hd hb h2 hsquare hroot hsim hm f y).val := by
  let := (negative_square_kernel_geometry Q hQ A d μ b hd hb h2
    hsquare hroot hsim hm).2.2.1
  let g := (negativeKernelCentralizerEquiv Q hQ A d μ b hd hb h2
    hsquare hroot hsim hm).symm f
  have heq : negativeKernelRestriction Q A b hb g =
      kernelInverseDual Q hQ A d μ b hd hb h2 hsquare hroot hsim hm f := by
    apply inverseDualAction_unique
    intro x z
    change Q.polarBilin (f x).val (negativeKernelRestriction Q A b hb g z).val =
      Q.polarBilin x.val z.val
    rw [negativeKernelRestriction_apply,
      ← negativeKernelCentralizerEquiv_symm_positive Q hQ A d μ b hd hb h2
        hsquare hroot hsim hm f x]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup g.val.property x.val z.val
  exact (negativeKernelRestriction_apply Q A b hb g y).symm.trans
    (congrArg (fun k : negativeSquareKernel A b ≃ₗ[K] negativeSquareKernel A b => (k y).val) heq)

end Negative

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
