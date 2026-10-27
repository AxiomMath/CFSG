module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84v_om5_false (hO5t : Sec8T84FactOm5Tab) {G : Type} [Group G] [Finite G] {t : G}
    {K K0 : Subgroup G} (hK : IsOm5Q K) (ht2 : orderOf t = 2)
    (htK : t ∈ normalizer (K : Set G))
    (hK0 : IsComponentIn K0 (K ⊓ centralizer ({t} : Set G))) (hL29 : IsL29 K0)
    (hinner : ∀ u ∈ K ⊓ centralizer ({t} : Set G), orderOf u = 2 → InnerOn K0 u) : False := by
  obtain ⟨u, hu, hu2, hnot⟩ := hO5t G K hK t ht2 htK K0 hK0 hL29
  exact hnot (hinner u hu hu2)

end CFSG.OddStandard.SmallF3.Omega
