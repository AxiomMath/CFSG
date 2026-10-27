module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HSData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

open CFSG.EvenSporadicStandard (StdHyp)

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.exists_isHSCover
    (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hZ : Nat.card (center L) = 2) (hq : IsSporadic (L ⧸ center L) .HS) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ L ∧
      IsHSCover (centralizer ({t} : Set G)) (L.subgroupOf (centralizer ({t} : Set G))) := by
  obtain ⟨t, ht2, hZt⟩ := exists_map_center_eq_zpowers hZ
  have htZ : t ∈ (center L).map L.subtype := hZt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := ((map_center_eq_inf_centralizer L) ▸ htZ).2
  have htL : t ∈ L := ((map_center_eq_inf_centralizer L) ▸ htZ).1
  have hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    h.centralizer_le_normalizer htC ht2
  have hLH : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
  have hinf := h.centralizer_inf_centralizer_eq_zpowers hS htC ht2
  have hEL : L.subgroupOf (centralizer ({t} : Set G)) ≃* L := subgroupOfEquivOfLe hLH
  refine ⟨t, ht2, htL, ?_⟩
  refine ⟨(normal_subgroupOf_iff_le_normalizer hLH).2 hHN, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := h.relIndex_sup_zpowers_dvd hS htC ht2
    rw [sup_eq_left.2 (zpowers_le.2 htL)] at h1
    exact h1.trans (index_dvd_two_of_isSporadic_hs hq)
  · have : Group.IsPerfect L := Group.isPerfect_def.2 h.standard.1.1
    exact Group.IsPerfect.ofSurjective (f := hEL.symm.toMonoidHom) hEL.symm.surjective
  · rw [Nat.card_congr (centerCongr hEL).toEquiv]
    exact hZ
  · obtain ⟨e⟩ := hq
    exact ⟨(QuotientGroup.congr _ _ hEL (map_center_eq hEL)).trans e⟩
  · intro x hx
    have hxL : (x : G) ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl
      have := mem_centralizer_iff.1 hx ⟨l, hLH hl⟩ hl
      exact congrArg Subtype.val this
    have hxt : (x : G) ∈ centralizer ({t} : Set G) := x.2
    have : (x : G) ∈ zpowers t := hinf ▸ ⟨hxL, hxt⟩
    exact zpowers_le.2 htL this

end CFSG.EvenSporadicStandard.TwoHS
