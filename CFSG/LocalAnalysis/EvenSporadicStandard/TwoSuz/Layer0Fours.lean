module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Layer0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore

section Certified


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_layer0_of_fours (h : StdHyp G L) (h2 : Nat.card (center L) = 2)
    (hQ : IsSporadic (L ⧸ center L) .Suz) (hFG : CFSG.EvenSmallLie.FoursGroupCondition L) :
    ∃ z : G, orderOf z = 2 ∧ (center L).map L.subtype = zpowers z ∧
      centralizer (L : Set G) = zpowers z ∧ L ≤ centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ≤ normalizer (L : Set G) ∧
      L.relIndex (centralizer ({z} : Set G)) ∣ 2 := by
  obtain ⟨z, hz2, hZz⟩ := exists_map_center_eq_zpowers h2
  have hrow := (HypOne.Suz.fullRowData_of_isSporadic hQ).rowData
  have hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2 := fun S =>
    h.card_sylow_eq_two_of_fours hrow.hypothesisOne hFG S
  have hzZ : z ∈ (center L).map L.subtype := hZz ▸ mem_zpowers z
  have hzC : z ∈ centralizer (L : Set G) := ((map_center_eq_inf_centralizer L) ▸ hzZ).2
  have hzL : z ∈ L := ((map_center_eq_inf_centralizer L) ▸ hzZ).1
  have hCz := (h.centralizer_eq_zpowers_of_mem_center hS hz2 hzZ).1
  refine ⟨z, hz2, hZz, hCz, fun l hl => ?_, h.centralizer_le_normalizer hzC hz2, ?_⟩
  · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hzC l hl)
  · have hd := h.relIndex_sup_centralizer_dvd hzC hz2
    rw [hCz, sup_eq_left.2 (zpowers_le.2 hzL)] at hd
    exact hd.trans (index_dvd_two_of_isSporadic_suz hQ)

end Certified

end CFSG.EvenSporadicStandard.TwoSuz
