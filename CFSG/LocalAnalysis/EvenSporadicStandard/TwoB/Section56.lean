module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Cover

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Open

variable {G : Type} [Group G]

theorem centralizer_ne_top_of_simple [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {ρ : G}
    (hρ : ρ ≠ 1) : centralizer ({ρ} : Set G) ≠ ⊤ := by
  intro h
  have hcen : ρ ∈ center G := by
    rw [mem_center_iff]
    intro g
    exact mem_centralizer_singleton_iff.1 (h ▸ mem_top g)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h0 | h0
  · exact hρ (mem_bot.1 (h0 ▸ hcen))
  · obtain ⟨a, b, hab⟩ := hnab
    exact hab (mem_center_iff.1 (h0 ▸ mem_top b) a)

variable [Finite G]

end CFSG.EvenSporadicStandard.TwoB
