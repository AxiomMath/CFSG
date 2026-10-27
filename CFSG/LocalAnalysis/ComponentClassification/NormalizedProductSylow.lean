module

public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProduct

public section

namespace CFSG.ComponentClassification.NormalizedProductSylow

@[expose] noncomputable def sylow {G : Type*} [Group G] [Finite G] (ambient acting : Subgroup G)
    (htwo : IsPGroup 2 acting) (hnormalizes : acting ≤ Subgroup.normalizer (ambient : Set G))
    (ambientSylow : Sylow 2 ambient)
    (hsylowNormalizes : acting ≤ Subgroup.normalizer
      ((((ambientSylow : Subgroup ambient).map ambient.subtype : Subgroup G) : Set G))) :
    Sylow 2 ↥(ambient ⊔ acting) := by
  let product := ambient ⊔ acting
  let sylowImage := (ambientSylow : Subgroup ambient).map ambient.subtype
  let smaller := sylowImage ⊔ acting
  have hsylowAmbient : sylowImage ≤ ambient := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hsmallerLe : smaller ≤ product := sup_le (hsylowAmbient.trans le_sup_left) le_sup_right
  have hsmallerTwo : IsPGroup 2 smaller :=
    (ambientSylow.isPGroup'.map ambient.subtype).to_sup_of_normal_left' htwo hsylowNormalizes
  refine ⟨smaller.subgroupOf product, hsmallerTwo.comap_subtype, ?_⟩
  intro overgroup hovergroupTwo hcontained
  let image := overgroup.map product.subtype
  have himageProduct : image ≤ product := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hsmallerImage : smaller ≤ image := by
    have hmap := Subgroup.map_mono (f := product.subtype) hcontained
    rw [Subgroup.map_subgroupOf_eq_of_le hsmallerLe] at hmap
    exact hmap
  have himageTwo : IsPGroup 2 image := hovergroupTwo.map product.subtype
  have hlocalTwo : IsPGroup 2 (image.subgroupOf ambient) := himageTwo.comap_subtype
  have hsylowContained : (ambientSylow : Subgroup ambient) ≤ image.subgroupOf ambient := by
    intro member hmember
    apply hsmallerImage
    exact (le_sup_left : sylowImage ≤ smaller) (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)
  have hequal := ambientSylow.is_maximal' hlocalTwo hsylowContained
  have himageSmaller : image ≤ smaller := by
    intro member hmember
    obtain ⟨left, hleft, right, hright, heq⟩ :=
      NormalizedProduct.coordinates ambient acting hnormalizes member (himageProduct hmember)
    have hrightImage : right ∈ image := hsmallerImage ((le_sup_right : acting ≤ smaller) hright)
    have hleftImage : left ∈ image := by
      have hmem := image.mul_mem hmember (image.inv_mem hrightImage)
      rw [← heq, mul_inv_cancel_right] at hmem
      exact hmem
    have hleftLocal : (⟨left, hleft⟩ : ambient) ∈ (ambientSylow : Subgroup ambient) := by
      rw [← hequal]
      exact hleftImage
    rw [← heq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_map.mpr ⟨⟨left, hleft⟩, hleftLocal, rfl⟩) hright
  apply le_antisymm _ hcontained
  intro member hmember
  exact himageSmaller (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)

theorem coe_sylow {G : Type*} [Group G] [Finite G] (ambient acting : Subgroup G)
    (htwo : IsPGroup 2 acting) (hnormalizes : acting ≤ Subgroup.normalizer (ambient : Set G))
    (ambientSylow : Sylow 2 ambient)
    (hsylowNormalizes : acting ≤ Subgroup.normalizer
      ((((ambientSylow : Subgroup ambient).map ambient.subtype : Subgroup G) : Set G))) :
    (sylow ambient acting htwo hnormalizes ambientSylow hsylowNormalizes : Subgroup ↥(ambient ⊔ acting)) =
      (((ambientSylow : Subgroup ambient).map ambient.subtype ⊔ acting).subgroupOf (ambient ⊔ acting)) := rfl

end CFSG.ComponentClassification.NormalizedProductSylow
