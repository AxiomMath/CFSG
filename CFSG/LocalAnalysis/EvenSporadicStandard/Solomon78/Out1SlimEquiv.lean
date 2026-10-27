module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1Slim

public section

namespace CFSG.EvenSporadicStandard.Solomon78

variable {Y Y' : Type} [Group Y] [Group Y']

theorem AllInner.of_mulEquiv (e : Y ≃* Y') (h : AllInner Y) : AllInner Y' := by
  intro α
  obtain ⟨s, hs⟩ := h ((e.trans α).trans e.symm)
  refine ⟨e s, MulEquiv.ext fun t => ?_⟩
  have h1 := congrArg (fun β : MulAut Y => e (β (e.symm t))) hs
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply, h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem InvolutionsCommute.of_mulEquiv (e : Y ≃* Y') (h : InvolutionsCommute Y) :
    InvolutionsCommute Y' := by
  intro u a hu ha
  obtain ⟨x, hx⟩ := h (e.symm u) (e.symm a) (by rw [MulEquiv.orderOf_eq, hu])
    (by rw [MulEquiv.orderOf_eq, ha])
  refine ⟨e x, ?_⟩
  have := congrArg e hx
  simpa [map_mul, map_inv] using this

end CFSG.EvenSporadicStandard.Solomon78
