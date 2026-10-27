module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5DescLayer
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem t5_component_le_layerCent {L : Subgroup G} {s : G} {J : Subgroup G}
    (hJ : IsComponentIn J (L ⊓ centralizer ({s} : Set G))) : J ≤ layerCent L s := by
  let H : Subgroup G := L ⊓ centralizer ({s} : Set G)
  have hJH : J ≤ H := hJ.1
  have hK : CFSG.IsComponent (J.subgroupOf H) := hJ.2
  have hle : J.subgroupOf H ≤ CFSG.layer H := CFSG.LocalCores.component_le_layer hK
  have hmap : (J.subgroupOf H).map H.subtype ≤ (CFSG.layer H).map H.subtype :=
    Subgroup.map_mono hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hJH] at hmap

theorem t5_component_normal_layerCent {L : Subgroup G} {s : G} {J : Subgroup G}
    (hJ : IsComponentIn J (L ⊓ centralizer ({s} : Set G))) :
    (J.subgroupOf (layerCent L s)).Normal := by
  let H : Subgroup G := L ⊓ centralizer ({s} : Set G)
  have hJH : J ≤ H := hJ.1
  have hK : CFSG.IsComponent (J.subgroupOf H) := hJ.2
  have hnorm : ((J.subgroupOf H).subgroupOf (CFSG.layer H)).Normal :=
    (CFSG.LocalCores.components_normal_in_layer hK).2
  have hle : J ≤ layerCent L s := t5_component_le_layerCent hJ
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h k hh hk
  have hhLc : h ∈ layerCent L s := hle hh
  have hkmap : k ∈ (CFSG.layer H).map H.subtype := hk
  have hhmap : h ∈ (CFSG.layer H).map H.subtype := hhLc
  obtain ⟨k', hk'L, hk'eq⟩ := Subgroup.mem_map.mp hkmap
  obtain ⟨h', hh'L, hh'eq⟩ := Subgroup.mem_map.mp hhmap
  have hHeq : h' = (⟨h, hJH hh⟩ : ↥H) := Subtype.ext (by simpa using hh'eq)
  have hk'val : (k'.val : G) = k := by simpa using hk'eq
  have hHlayer : (⟨h, hJH hh⟩ : ↥H) ∈ CFSG.layer H := by
    rw [← hHeq]
    exact hh'L
  let hL : ↥(CFSG.layer H) := ⟨⟨h, hJH hh⟩, hHlayer⟩
  have hLmem : hL ∈ (J.subgroupOf H).subgroupOf (CFSG.layer H) := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.mpr hh
  let kL : ↥(CFSG.layer H) := ⟨k', hk'L⟩
  have hconj := hnorm.conj_mem hL hLmem kL
  have hconjval : ((kL * hL * kL⁻¹ : ↥(CFSG.layer H)).val : ↥H).val = k * h * k⁻¹ := by
    simp [hL, kL, hk'val]
  have hmem : ((kL * hL * kL⁻¹ : ↥(CFSG.layer H)).val : ↥H).val ∈ J :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hconj)
  rwa [hconjval] at hmem

theorem t5_component_subgroupOf_normalizer {L : Subgroup G} {s : G}
    (hs : s ∈ normalizer (L : Set G)) {J : Subgroup G}
    (hJ : IsComponentIn J (L ⊓ centralizer ({s} : Set G))) :
    J.subgroupOf (normalizer (L : Set G)) ≤
        CFSG.inSubgroup CFSG.layer (descCent L hs) ∧
      ((J.subgroupOf (normalizer (L : Set G))).subgroupOf
        (CFSG.inSubgroup CFSG.layer (descCent L hs))).Normal ∧
      Nat.card ↥(J.subgroupOf (normalizer (L : Set G))) = Nat.card ↥J := by
  let H : Subgroup G := L ⊓ centralizer ({s} : Set G)
  have hJle : J ≤ layerCent L s := t5_component_le_layerCent hJ
  have hlcN : layerCent L s ≤ normalizer (L : Set G) :=
    (Subgroup.map_subtype_le (CFSG.layer H)).trans
      ((inf_le_left : H ≤ L).trans (Subgroup.le_normalizer (H := L)))
  have hJN : J ≤ normalizer (L : Set G) := hJle.trans hlcN
  have hsub : J.subgroupOf (normalizer (L : Set G)) ≤
      CFSG.inSubgroup CFSG.layer (descCent L hs) := by
    intro x hx
    have hxJ : x.val ∈ J := Subgroup.mem_subgroupOf.mp hx
    have hxLc : x.val ∈ layerCent L s := hJle hxJ
    have hxmap : x.val ∈
        (CFSG.inSubgroup CFSG.layer (descCent L hs)).map
          (normalizer (L : Set G)).subtype := by
      rw [← t5_layerCent_eq_map L hs]
      exact hxLc
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hxmap
    have hyx : y = x := Subtype.ext (by simpa using hyeq)
    rwa [hyx] at hy
  refine ⟨hsub, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hsub]
    intro h k hh hk
    have hhJ : h.val ∈ J := Subgroup.mem_subgroupOf.mp hh
    have hkLc : k.val ∈ layerCent L s := by
      have hkm : k.val ∈
          (CFSG.inSubgroup CFSG.layer (descCent L hs)).map
            (normalizer (L : Set G)).subtype :=
        Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
      rwa [← t5_layerCent_eq_map L hs] at hkm
    have hnorm := (Subgroup.normal_subgroupOf_iff hJle).mp
      (t5_component_normal_layerCent hJ)
    have hmem : k.val * h.val * k.val⁻¹ ∈ J := hnorm h.val k.val hhJ hkLc
    rw [Subgroup.mem_subgroupOf]
    simpa using hmem
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJN).toEquiv

end CFSG.OddStandard.SmallF3.Omega
