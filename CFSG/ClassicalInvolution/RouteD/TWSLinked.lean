module

public import CFSG.ClassicalInvolution.SmallCases.TwinChainDefs

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z w : G}

theorem le_centralizer_of_commutes (hz : z ∈ K) {N : Subgroup G} (h : Commutes K N) :
    N ≤ Subgroup.centralizer ({z} : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (h z hz n hn).symm

theorem linkedAtProduct_iff (hz : z ∈ K) (hKz : K ≤ Subgroup.centralizer ({z} : Set G))
    (hiso : ∀ N ∈ centralizingMembers Ω {z}, N ≠ K → Commutes K N) :
    LinkedAtProduct Ω K z w ↔
      ∃ N ∈ centralizingMembers Ω {z * w}, ¬ N ≤ Subgroup.centralizer ({z} : Set G) := by
  constructor
  · rintro ⟨N, hN, hne, hnc⟩
    refine ⟨N, hN, fun hle => hnc ?_⟩
    exact hiso N ⟨hN.1, hle⟩ hne
  · rintro ⟨N, hN, hnle⟩
    refine ⟨N, hN, fun h => hnle (h ▸ hKz), fun hc => hnle ?_⟩
    exact le_centralizer_of_commutes hz hc

end CFSG.ClassicalInvolution.RouteD.TWS
