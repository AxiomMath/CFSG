module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem StdHyp.component_of_involution (h : StdHyp G L) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    L ≤ centralizer ({t} : Set G) ∧
      (L.subgroupOf (centralizer ({t} : Set G))).IsSubnormal := by
  have hle : L ≤ centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 ht x hx)
  exact ⟨hle, ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
    (h.centralizer_le_normalizer ht ht2)).isSubnormal⟩

theorem StdHyp.exists_involution_component (h : StdHyp G L) :
    ∃ t : G, orderOf t = 2 ∧ L ≤ centralizer ({t} : Set G) ∧
      (L.subgroupOf (centralizer ({t} : Set G))).IsSubnormal := by
  obtain ⟨t, ht, ht2⟩ := h.exists_involution_centralizer
  exact ⟨t, ht2, h.component_of_involution ht ht2⟩

end CFSG.EvenSporadicStandard
