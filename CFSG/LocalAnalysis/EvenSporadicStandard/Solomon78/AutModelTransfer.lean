module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.AutModelRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransfer

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SmallOddCore

variable {M : Type} [Group M] {P R : Subgroup M}

theorem AutRowData.outTwo (d : AutRowData P R) : OutTwo ↥P := by
  have h := d.model
  have inner : ∀ γ : MulAut ↥P, h.elt γ ∈ P → ∃ l : P, γ = MulAut.conj l := by
    intro γ hγ
    refine ⟨⟨h.elt γ, hγ⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
    rw [h.elt_spec γ]
    rfl
  intro α β
  by_cases ha : h.elt α ∈ P
  · exact Or.inl (inner α ha)
  by_cases hb : h.elt β ∈ P
  · exact Or.inr (Or.inl (inner β hb))
  refine Or.inr (Or.inr (inner (α⁻¹ * β) ?_))
  rw [← h.hom_apply, map_mul, map_inv, h.hom_apply, h.hom_apply]
  exact d.index _ (h.elt_mem α) ha _ (h.elt_mem β) hb

end CFSG.EvenSporadicStandard.Solomon78
