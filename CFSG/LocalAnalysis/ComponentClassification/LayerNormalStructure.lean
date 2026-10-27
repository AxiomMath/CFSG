module

public import CFSG.LocalAnalysis.ComponentClassification.Layer

public section

open CFSG.Open

namespace CFSG.ComponentClassification.LayerNormalStructure

local instance intrinsicLayerNormal {G : Type*} [Group G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] :
    ((Layer.subgroup normalSubgroup).map normalSubgroup.subtype).Normal := by
  let : (Layer.subgroup normalSubgroup).Characteristic := Layer.characteristic normalSubgroup
  exact ConjAct.normal_of_characteristic_of_normal

theorem normal_monotone {G : Type*} [Group G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] :
    (Layer.subgroup normalSubgroup).map normalSubgroup.subtype ≤ Layer.subgroup G := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro component hcomponent
  exact Subgroup.map_le_iff_le_comap.mp (Layer.component_le
    (LocalComponents.of_subnormal_subgroup normalSubgroup
      (Components.chain_of_mathlib_subnormal
        (inferInstance : normalSubgroup.Normal).isSubnormal) component hcomponent))

theorem quotient_layer_centralizes {G : Type*} [Group G] [Finite G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] :
    (Layer.subgroup G).map
      (QuotientGroup.mk' ((Layer.subgroup normalSubgroup).map normalSubgroup.subtype)) ≤
      Subgroup.centralizer
        (normalSubgroup.map
          (QuotientGroup.mk' ((Layer.subgroup normalSubgroup).map normalSubgroup.subtype)) :
            Set (G ⧸ (Layer.subgroup normalSubgroup).map normalSubgroup.subtype)) := by
  let intrinsicLayer := (Layer.subgroup normalSubgroup).map normalSubgroup.subtype
  let : (Layer.subgroup normalSubgroup).Characteristic := Layer.characteristic normalSubgroup
  let : intrinsicLayer.Normal := ConjAct.normal_of_characteristic_of_normal
  let projection := QuotientGroup.mk' intrinsicLayer
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro component hcomponent
  apply Subgroup.map_le_iff_le_comap.mp
  rcases LocalComponents.normal_contains_or_commutes component normalSubgroup hcomponent with
    hcomponentLe | hcommutes
  · have hle : component ≤ intrinsicLayer := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hcomponentLe]
      exact Subgroup.map_mono
        (Layer.component_le (LocalComponents.of_overgroup hcomponent hcomponentLe))
    have hkilled : component.map projection = ⊥ :=
      component.map_eq_bot_iff.mpr (by rwa [QuotientGroup.ker_mk'])
    rw [hkilled]
    exact bot_le
  · intro member hmember
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    obtain ⟨otherLift, hotherLift, rfl⟩ := Subgroup.mem_map.mp hother
    have heq := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes hlift)
        otherLift hotherLift
    simpa only [map_mul] using congrArg projection heq

theorem perfect_normal_contained {G : Type*} [Group G] [Finite G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] [Group.IsPerfect normalSubgroup]
    (hcontained : normalSubgroup ≤ Layer.subgroup G) :
    (Layer.subgroup normalSubgroup).map normalSubgroup.subtype = normalSubgroup := by
  let intrinsicLayer := (Layer.subgroup normalSubgroup).map normalSubgroup.subtype
  let : (Layer.subgroup normalSubgroup).Characteristic := Layer.characteristic normalSubgroup
  let : intrinsicLayer.Normal := ConjAct.normal_of_characteristic_of_normal
  let projection := QuotientGroup.mk' intrinsicLayer
  have hcentralizes := quotient_layer_centralizes normalSubgroup
  have himageLe := Subgroup.map_mono (f := projection) hcontained
  let : Group.IsPerfect (normalSubgroup.map projection) :=
    Group.IsPerfect.map projection
  let : IsMulCommutative (normalSubgroup.map projection) :=
    isMulCommutative_iff.mpr fun left right => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hcentralizes (himageLe left.property))
        right.val right.property).symm
  have hbot : normalSubgroup.map projection = ⊥ :=
    (normalSubgroup.map projection).eq_bot_of_subsingleton
  have hle : normalSubgroup ≤ intrinsicLayer := by
    have hkernel := normalSubgroup.map_eq_bot_iff.mp hbot
    rwa [QuotientGroup.ker_mk'] at hkernel
  exact le_antisymm (by
    rintro member ⟨lift, _, rfl⟩
    exact lift.property) hle

theorem layer_top_of_perfect_normal_contained {G : Type*} [Group G] [Finite G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] [Group.IsPerfect normalSubgroup]
    (hcontained : normalSubgroup ≤ Layer.subgroup G) : Layer.subgroup normalSubgroup = ⊤ := by
  apply top_unique
  intro member _
  have hmem : member.val ∈ (Layer.subgroup normalSubgroup).map normalSubgroup.subtype := by
    rw [perfect_normal_contained normalSubgroup hcontained]
    exact member.property
  obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp hmem
  rwa [show lift = member from Subtype.ext heq] at hlift

end CFSG.ComponentClassification.LayerNormalStructure
