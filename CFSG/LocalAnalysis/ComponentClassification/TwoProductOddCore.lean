module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionOddIntersection
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProduct

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoProductOddCore

theorem core_le_normal {G : Type*} [Group G] [Finite G] (normal : Subgroup G) [normal.Normal]
    (hquotient : IsPGroup 2 (G ⧸ normal)) : componentClassificationOddCore G ≤ normal := by
  let quotient := QuotientGroup.mk' normal
  have hodd : Odd (Nat.card ((componentClassificationOddCore G).map quotient)) :=
    (OddCore.odd_card G).of_dvd_nat (Subgroup.card_map_dvd (componentClassificationOddCore G) quotient)
  have hbot := TwoActionOddIntersection.two_in_odd_eq_bot ((componentClassificationOddCore G).map quotient)
    ((componentClassificationOddCore G).map quotient) (hquotient.to_subgroup _) hodd le_rfl
  have hle := (Subgroup.map_eq_bot_iff (componentClassificationOddCore G)).mp hbot
  change componentClassificationOddCore G ≤ (QuotientGroup.mk' normal).ker at hle
  rwa [QuotientGroup.ker_mk'] at hle

theorem quotient_two {G : Type*} [Group G] (normal acting : Subgroup G)
    (hnormalizes : acting ≤ Subgroup.normalizer (normal : Set G)) (htwo : IsPGroup 2 acting) :
    let product := normal ⊔ acting
    let localNormal := normal.subgroupOf product
    let localNormality : localNormal.Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hnormalizes)
    letI := localNormality
    IsPGroup 2 (product ⧸ localNormal) := by
  let product := normal ⊔ acting
  let localNormal := normal.subgroupOf product
  let : localNormal.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le Subgroup.le_normalizer hnormalizes)
  let quotient := QuotientGroup.mk' localNormal
  let inclusion := Subgroup.inclusion (le_sup_right : acting ≤ product)
  have hsurjective : Function.Surjective (quotient.comp inclusion) := by
    intro member
    obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective localNormal member
    obtain ⟨left, hleft, right, hright, heq⟩ := NormalizedProduct.coordinates normal acting hnormalizes
      lift.val lift.property
    have hleftProduct : left ∈ product := (le_sup_left : normal ≤ product) hleft
    have hrightProduct : right ∈ product := (le_sup_right : acting ≤ product) hright
    have hproductEq : (⟨left, hleftProduct⟩ : product) * ⟨right, hrightProduct⟩ = lift := Subtype.ext heq
    have hleftOne : quotient (⟨left, hleftProduct⟩ : product) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hleft
    refine ⟨⟨right, hright⟩, ?_⟩
    change quotient (⟨right, hrightProduct⟩ : product) = member
    calc
      _ = quotient ((⟨left, hleftProduct⟩ : product) * ⟨right, hrightProduct⟩) := by
        rw [map_mul, hleftOne, one_mul]
      _ = member := by rw [hproductEq]; exact hlift
  exact htwo.of_surjective (quotient.comp inclusion) hsurjective

theorem image_eq {G : Type*} [Group G] [Finite G] (normal acting : Subgroup G)
    (hnormalizes : acting ≤ Subgroup.normalizer (normal : Set G)) (htwo : IsPGroup 2 acting) :
    (componentClassificationOddCore ↥(normal ⊔ acting)).map (normal ⊔ acting).subtype =
      (componentClassificationOddCore normal).map normal.subtype := by
  let product := normal ⊔ acting
  let localNormal := normal.subgroupOf product
  let : localNormal.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le Subgroup.le_normalizer hnormalizes)
  have hquotient : IsPGroup 2 (product ⧸ localNormal) := quotient_two normal acting hnormalizes htwo
  have hle := core_le_normal localNormal hquotient
  have hintersection := OddCore.normal_intersection product localNormal
  rw [inf_eq_right.mpr hle] at hintersection
  have hmap := congrArg (Subgroup.map product.subtype) hintersection
  rw [Subgroup.map_map] at hmap
  rw [← hmap]
  let equivalence : localNormal ≃* normal := Subgroup.subgroupOfEquivOfLe (le_sup_left : normal ≤ product)
  have hequiv := OddCore.equiv_invariant equivalence
  have hcoreMap := congrArg (Subgroup.map normal.subtype) hequiv
  rw [Subgroup.map_map] at hcoreMap
  convert hcoreMap using 1
  congr 1

end CFSG.ComponentClassification.TwoProductOddCore
