module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowAut

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78.Fi24Row
open CFSG.Sporadic.Fi24 (R JR tR D24 index_JR)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fi24_outTwo_P : OutTwo ↥(JR : Subgroup R) := by
  intro α β
  obtain ⟨r, -, hr⟩ := fi24_autModel.surj α
  obtain ⟨r', -, hr'⟩ := fi24_autModel.surj β
  have hconj : ∀ (γ : MulAut ↥(JR : Subgroup R)) (s : R),
      (∀ p : ↥(JR : Subgroup R), ((γ p : ↥(JR : Subgroup R)) : R) = s * p * s⁻¹) →
        s ∈ JR → ∃ l : ↥(JR : Subgroup R), γ = MulAut.conj l := by
    intro γ s hs hsJ
    refine ⟨⟨s, hsJ⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
    rw [hs p]
    rfl
  by_cases h1 : r ∈ JR
  · exact Or.inl (hconj α r hr h1)
  by_cases h2 : r' ∈ JR
  · exact Or.inr (Or.inl (hconj β r' hr' h2))
  right
  right
  have h3 : r⁻¹ * r' ∈ JR := by
    rw [Subgroup.mul_mem_iff_of_index_two index_JR]
    exact iff_of_false (fun h => h1 ((inv_mem_iff).1 h)) h2
  refine hconj (α⁻¹ * β) (r⁻¹ * r') ?_ h3
  intro p
  have hz : α ((α⁻¹ * β) p) = β p := by
    rw [MulAut.mul_apply, MulAut.apply_inv_self]
  have e1 : (((α ((α⁻¹ * β) p) : ↥(JR : Subgroup R)) : R)) = r * ((α⁻¹ * β) p : R) * r⁻¹ :=
    hr _
  rw [hz, hr' p] at e1
  calc (((α⁻¹ * β) p : ↥(JR : Subgroup R)) : R)
      = r⁻¹ * (r * ((α⁻¹ * β) p : R) * r⁻¹) * r := by group
    _ = r⁻¹ * (r' * p * r'⁻¹) * r := by rw [← e1]
    _ = r⁻¹ * r' * p * (r⁻¹ * r')⁻¹ := by group

end CFSG.EvenSporadicStandard.Solomon78
