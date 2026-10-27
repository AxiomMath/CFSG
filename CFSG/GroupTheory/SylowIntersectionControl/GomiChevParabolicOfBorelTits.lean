module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.LieType.BorelTits.RadicalParabolic
import CFSG.GroupTheory.PCore.SubgroupOfNormalizer

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools

theorem gomiChevParabolic_of_borelTits (h : GomiChevBorelTits) : GomiChevParabolic := by
  intro G _ _ L I hL hIL _hIp hrad
  have hBT : CFSG.LieType.BorelTits.Holds ↥L 2 := h ↥L hL
  let R : Subgroup ↥L := I.subgroupOf L
  have hmap := map_subtype_pCoreOf_normalizer_subgroupOf 2 hIL (X := L) (T := I)
  change (pCoreOf 2 (Subgroup.normalizer (R : Set ↥L))).map L.subtype =
    pCoreOf 2 (L ⊓ Subgroup.normalizer (I : Set G)) at hmap
  rw [hrad] at hmap
  have hR : pCoreOf 2 (Subgroup.normalizer (R : Set ↥L)) = R := by
    refine (Subgroup.map_subtype_inj (H := L)).mp ?_
    rw [hmap, Subgroup.map_subgroupOf_eq_of_le hIL]
  obtain ⟨S, hS⟩ :=
    CFSG.LieType.BorelTits.Holds.exists_sylow_normalizer_le_normalizer hBT hR
  refine ⟨(S : Subgroup ↥L).map L.subtype, ⟨S, rfl⟩, ?_⟩
  intro x hx
  rw [Subgroup.mem_inf] at hx ⊢
  obtain ⟨hxL, hxN⟩ := hx
  refine ⟨hxL, ?_⟩
  have hUL : ((S : Subgroup ↥L).map L.subtype) ≤ L := Subgroup.map_subtype_le _
  have hUS : (((S : Subgroup ↥L).map L.subtype).subgroupOf L) = (S : Subgroup ↥L) :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective (S : Subgroup ↥L)
  have hUnorm : (Subgroup.normalizer (((S : Subgroup ↥L).map L.subtype) : Set G)).subgroupOf L =
      Subgroup.normalizer (((S : Subgroup ↥L)) : Set ↥L) := by
    rw [Subgroup.subgroupOf_normalizer_eq hUL, hUS]
  have hxS : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer (((S : Subgroup ↥L)) : Set ↥L) := by
    rw [← hUnorm, Subgroup.mem_subgroupOf]
    exact hxN
  have hxR : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer (R : Set ↥L) := hS hxS
  have hxNI : (⟨x, hxL⟩ : ↥L) ∈ (Subgroup.normalizer (I : Set G)).subgroupOf L := by
    rw [Subgroup.subgroupOf_normalizer_eq hIL]
    exact hxR
  rwa [Subgroup.mem_subgroupOf] at hxNI

end CFSG.GroupTheory
