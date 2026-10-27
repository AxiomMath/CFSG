module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidualConjBase

public section

namespace CFSG.GroupTheory.ThreeTranspositions

variable {X : Type} [Group X]

theorem exists_mulEquiv_threeResidualQuot_of_isConj {d d₀ : X} (hc : IsConj d d₀)
    {M : Type*} [Group M] {P : M → Prop} (φ : ↥(threeResidualQuot d) ≃* M)
    (hφ : ∀ g, g ∈ threeResidualClass d ↔ P (φ g)) :
    ∃ φ₀ : ↥(threeResidualQuot d₀) ≃* M, ∀ g, g ∈ threeResidualClass d₀ ↔ P (φ₀ g) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  refine ⟨(threeResidualQuotConjEquiv c d).symm.trans φ, fun y => ?_⟩
  have := hφ ((threeResidualQuotConjEquiv c d).symm y)
  rw [← mem_threeResidualClass_conj_iff c d, MulEquiv.apply_symm_apply] at this
  rw [this]
  rfl

end CFSG.GroupTheory.ThreeTranspositions
