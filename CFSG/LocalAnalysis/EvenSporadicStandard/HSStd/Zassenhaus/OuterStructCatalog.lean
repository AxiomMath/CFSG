module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.NoAbelianNormal
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd

theorem centralizer_singleton_ne_top {G : Type} [Group G] (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) {v : G} (hv1 : v ≠ 1) :
    centralizer ({v} : Set G) ≠ ⊤ := by
  intro h
  have hc : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h' | h'
    · exact h'
    · obtain ⟨a, b, hab⟩ := hna
      exact absurd (mem_center_iff.mp (h' ▸ mem_top b) a) hab
  apply hv1
  have hv : v ∈ center G := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({v} : Set G) := h ▸ mem_top g
    exact mem_centralizer_singleton_iff.1 hg
  rw [hc, mem_bot] at hv
  exact hv

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
