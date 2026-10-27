module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSize
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonAmbient

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem maximumAbelianOrder_mono_subgroups {G : Type u} [Group G] [Finite G]
    (smaller larger : Subgroup G) (hle : smaller ≤ larger) :
    maximumAbelianOrder smaller ≤ maximumAbelianOrder larger := by
  obtain ⟨maximum, hmaximum⟩ := exists_maximumOrderAbelian smaller
  have hmapComm := subgroup_map_commutative maximum (Subgroup.inclusion hle) hmaximum.1
  have hbound := commutative_card_le_maximumAbelianOrder (maximum.map (Subgroup.inclusion hle)) hmapComm
  rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hle), hmaximum.2] at hbound

theorem ambientMaximum_commutative {G : Type u} [Group G]
    (abelian overgroup : Subgroup G) (hle : abelian ≤ overgroup)
    (hmaximum : MaximumOrderAbelian (abelian.subgroupOf overgroup)) : IsMulCommutative abelian := by
  have hmapComm := subgroup_map_commutative (abelian.subgroupOf overgroup) overgroup.subtype hmaximum.1
  rwa [Subgroup.map_subgroupOf_eq_of_le hle] at hmapComm

theorem maximumAbelianOrder_eq_of_common_maximum {G : Type u} [Group G] [Finite G]
    (abelian smaller larger : Subgroup G) (hab : abelian ≤ smaller) (hle : smaller ≤ larger)
    (hmaximum : MaximumOrderAbelian (abelian.subgroupOf larger)) :
    maximumAbelianOrder smaller = maximumAbelianOrder larger := by
  have hcomm := ambientMaximum_commutative abelian larger (hab.trans hle) hmaximum
  have : IsMulCommutative abelian := hcomm
  have hsmallComm : IsMulCommutative (abelian.subgroupOf smaller) := inferInstance
  have hbound := commutative_card_le_maximumAbelianOrder (abelian.subgroupOf smaller) hsmallComm
  have hcard : Nat.card (abelian.subgroupOf larger) = Nat.card abelian :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hab.trans hle)).toEquiv
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hab).toEquiv, ← hcard, hmaximum.2] at hbound
  exact le_antisymm (maximumAbelianOrder_mono_subgroups smaller larger hle) hbound

theorem ambientMaximum_restrict {G : Type u} [Group G] [Finite G]
    (abelian smaller larger : Subgroup G) (hab : abelian ≤ smaller) (hle : smaller ≤ larger)
    (hmaximum : MaximumOrderAbelian (abelian.subgroupOf larger)) :
    MaximumOrderAbelian (abelian.subgroupOf smaller) := by
  have : IsMulCommutative abelian := ambientMaximum_commutative abelian larger (hab.trans hle) hmaximum
  refine ⟨inferInstance, ?_⟩
  change Nat.card ↥(abelian.subgroupOf smaller) = maximumAbelianOrder smaller
  rw [maximumAbelianOrder_eq_of_common_maximum abelian smaller larger hab hle hmaximum]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hab).toEquiv,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hab.trans hle)).toEquiv]
  exact hmaximum.2

theorem thompsonCenterOf_le_of_common_maximum {G : Type u} [Group G] [Finite G]
    (abelian smaller larger : Subgroup G) (hab : abelian ≤ smaller) (hle : smaller ≤ larger)
    (hmaximum : MaximumOrderAbelian (abelian.subgroupOf larger)) :
    thompsonCenterOf larger ≤ thompsonCenterOf smaller := by
  have horders := maximumAbelianOrder_eq_of_common_maximum abelian smaller larger hab hle hmaximum
  have hcenterLe : thompsonCenterOf larger ≤ abelian := by
    have hbound : thompsonOrderCenter larger ≤ abelian.subgroupOf larger := by
      rw [thompsonOrderCenter_eq_intersection]
      exact iInf_le _ (⟨abelian.subgroupOf larger, hmaximum⟩ : {candidate : Subgroup larger // MaximumOrderAbelian candidate})
    have hmapped := Subgroup.map_mono (f := larger.subtype) hbound
    rwa [Subgroup.map_subgroupOf_eq_of_le (hab.trans hle)] at hmapped
  intro element helement
  have hsmallMem : element ∈ smaller := hab (hcenterLe helement)
  refine Subgroup.mem_map.mpr ⟨⟨element, hsmallMem⟩, ?_, rfl⟩
  change (⟨element, hsmallMem⟩ : smaller) ∈ thompsonOrderCenter smaller
  rw [thompsonOrderCenter_eq_intersection]
  apply Subgroup.mem_iInf.mpr
  intro candidate
  let mapped := candidate.val.map (Subgroup.inclusion hle)
  have hmappedMaximum : MaximumOrderAbelian mapped := by
    refine ⟨subgroup_map_commutative candidate.val (Subgroup.inclusion hle) candidate.property.1, ?_⟩
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hle), candidate.property.2]
    exact horders
  obtain ⟨representative, hrepresentative, heq⟩ := helement
  have hmem : representative ∈ mapped := by
    change representative ∈ thompsonOrderCenter larger at hrepresentative
    rw [thompsonOrderCenter_eq_intersection] at hrepresentative
    exact (iInf_le (fun candidate : {candidate : Subgroup larger // MaximumOrderAbelian candidate} => candidate.val)
      ⟨mapped, hmappedMaximum⟩) hrepresentative
  obtain ⟨preimage, hpreimage, hpreimageEq⟩ := hmem
  have hsame : preimage = (⟨element, hsmallMem⟩ : smaller) := by
    apply Subtype.ext
    have hambient := congrArg (fun value : larger => (value : G)) hpreimageEq
    exact hambient.trans heq
  exact hsame ▸ hpreimage

end CFSG.RankThreeEvenClassification.Helpers
