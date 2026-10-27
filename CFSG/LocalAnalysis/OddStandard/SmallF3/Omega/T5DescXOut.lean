module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5DescLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5GrpPCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem t5_desc_xout_eq_layer (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) {s : G} (hs : s ∈ normalizer (L : Set G))
    (h : XOut (DescL L t) (descElt L t s hs) = layerCent (DescL L t) (descElt L t s hs)) :
    XOut L s = layerCent L s := by
  have hmap : (twoPrimeRes (twoRes (descCent L hs))).map (descMk L t) =
      (CFSG.inSubgroup CFSG.layer (descCent L hs)).map (descMk L t) := by
    rw [← t5_desc_xout hL ht ht2 hs, ← t5_desc_layerCent hL ht ht2 hs]
    exact h
  have hCn : twoPrimeRes (twoRes (descCent L hs)) =
      CFSG.inSubgroup CFSG.layer (descCent L hs) :=
    t5_xout_eq_layer (descMk L t) (descT_mem_center hL ht ht2) (descT_mul_self ht ht2)
      (descMk_ker_le_zpowers hL ht ht2) (descT_mem_descCent hL ht ht2 hs) hmap
  rw [t5_xout_eq_map L hs, t5_layerCent_eq_map L hs, hCn]

theorem t5_desc_xout_eq_pCore (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) {s : G} (hs : s ∈ normalizer (L : Set G))
    (h : XOut (DescL L t) (descElt L t s hs) =
      CFSG.inSubgroup (CFSG.pCore 2)
        (twoRes (DescL L t ⊓ centralizer ({descElt L t s hs} : Set (DescG L t))))) :
    XOut L s = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G))) := by
  let Cn : Subgroup ↥(normalizer (L : Set G)) := descCent L hs
  let Dn : Subgroup ↥(normalizer (L : Set G)) := twoRes Cn
  let f : ↥(normalizer (L : Set G)) →* DescG L t := descMk L t
  have h2f : ∀ k ∈ f.ker, k * k = 1 := descMk_ker_sq hL ht ht2
  have h2ι : ∀ k ∈ (normalizer (L : Set G)).subtype.ker, k * k = 1 := by
    intro k hk
    rw [Subgroup.ker_subtype, Subgroup.mem_bot] at hk
    rw [hk, mul_one]
  have hmap : (twoPrimeRes Dn).map f = (CFSG.inSubgroup (CFSG.pCore 2) Dn).map f := by
    rw [← t5_desc_xout hL ht ht2 hs, ← t5_map_inSubgroup_pCore f h2f Dn,
      ← t5_desc_twoRes_cent hL ht ht2 hs]
    exact h
  have hDn : twoPrimeRes Dn = CFSG.inSubgroup (CFSG.pCore 2) Dn :=
    t5_xout_eq_pCore f h2f Dn hmap
  rw [t5_xout_eq_map L hs, hDn, t5_twoRes_cent_eq L hs, t5_map_inSubgroup_pCore _ h2ι Dn]

end CFSG.OddStandard.SmallF3.Omega
