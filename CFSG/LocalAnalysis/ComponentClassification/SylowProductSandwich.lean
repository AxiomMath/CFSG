module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.SylowProductSandwich

theorem collapse {G : Type*} [Group G] [Finite G]
    (first second : Subgroup G) (bound : ℕ)
    (hfirst : Nat.card first = bound) (hproduct : Nat.card ↥(first ⊔ second) ≤ bound) :
    first ⊔ second = first ∧ second ≤ first := by
  have heq : first = first ⊔ second := Subgroup.eq_of_le_of_card_ge le_sup_left (by simpa only [hfirst] using hproduct)
  exact ⟨heq.symm, heq.symm ▸ (le_sup_right : second ≤ first ⊔ second)⟩

theorem sandwich {G : Type*} [Group G] [Finite G]
    (first second middle : Subgroup G)
    (hproduct : Nat.card ↥(first ⊔ second) ≤ Nat.card middle) (hmiddle : Nat.card middle ≤ Nat.card first) :
    first ⊔ second = first ∧ second ≤ first ∧ Nat.card middle = Nat.card first := by
  obtain ⟨hcollapse, hcontained⟩ := collapse first second (Nat.card first) rfl (hproduct.trans hmiddle)
  refine ⟨hcollapse, hcontained, le_antisymm hmiddle ?_⟩
  rwa [hcollapse] at hproduct

theorem intersection_center {G : Type*} [Group G]
    (first second : Subgroup G) (hcommutes : ⁅first, second⁆ = ⊥)
    (subgroup : Subgroup G) (hfirst : subgroup ≤ first) (hsecond : subgroup ≤ second) :
    subgroup ≤ (Subgroup.center first).map first.subtype := by
  have hcentral := Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes)
  intro member hmember
  refine Subgroup.mem_map.mpr ⟨⟨member, hfirst hmember⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentral (hsecond hmember)) other.val other.property)

end CFSG.ComponentClassification.SylowProductSandwich
