module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionTwoExtension

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

variable {G A : Type*} [Group G] [Group A]

theorem semidirect_base_normal (φ : A →* MulAut G) :
    (SemidirectProduct.inl (φ := φ)).range.Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

theorem semidirect_fixed_commute (φ : A →* MulAut G) (a : A) (g : G)
    (hfixed : φ a g = g) :
    Commute (SemidirectProduct.inr a : G ⋊[φ] A) (SemidirectProduct.inl g) := by
  have hconj := SemidirectProduct.inl_aut (φ := φ) a g
  rw [hfixed] at hconj
  have hmul := congrArg (fun x : G ⋊[φ] A => x * SemidirectProduct.inr a) hconj
  apply Eq.symm
  simpa only [map_inv, inv_mul_cancel_right] using hmul

variable [Finite G] [Finite A]

theorem semidirect_finite (φ : A →* MulAut G) : Finite (G ⋊[φ] A) :=
  Finite.of_equiv (G × A) (SemidirectProduct.equivProd (φ := φ)).symm

end CFSG.ComponentClassification.AschbacherComponentInvolution
