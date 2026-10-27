module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidualConjBase

public section

namespace CFSG.GroupTheory.ThreeTranspositions

variable {X : Type} [Group X]

theorem fischerLinearModel_conj {g d : X} {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing F] {H : Subgroup (GL ι F)} {T : Set (GL ι F)}
    (h : CFSG.Open.fischerLinearModel (threeResidualClass d) H T) :
    CFSG.Open.fischerLinearModel (threeResidualClass (g * d * g⁻¹)) H T := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨(threeResidualQuotConjEquiv g d).symm.trans φ, fun y => ?_⟩
  have := hφ ((threeResidualQuotConjEquiv g d).symm y)
  rw [← mem_threeResidualClass_conj_iff g d, MulEquiv.apply_symm_apply] at this
  rw [this]
  rfl

theorem fischerLinearModel_of_isConj {d d₀ : X} (hc : IsConj d d₀) {ι F : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing F] {H : Subgroup (GL ι F)} {T : Set (GL ι F)}
    (h : CFSG.Open.fischerLinearModel (threeResidualClass d) H T) :
    CFSG.Open.fischerLinearModel (threeResidualClass d₀) H T := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact fischerLinearModel_conj h

end CFSG.GroupTheory.ThreeTranspositions
