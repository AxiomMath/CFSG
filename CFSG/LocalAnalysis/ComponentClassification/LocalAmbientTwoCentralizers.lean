module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCommutingActions

public section

open CFSG.Open

namespace CFSG.ComponentClassification.LocalAmbientTwoCentralizers

theorem component_le_centralizer {G : Type*} [Group G] [Finite G]
    (twoSubgroup normalTwo : Subgroup G) (htwo : IsPGroup 2 twoSubgroup)
    [normalTwo.Normal] (hnormalTwo : IsPGroup 2 normalTwo)
    (component : Subgroup (Subgroup.normalizer (twoSubgroup : Set G)))
    (hcomponent : TwoComponents.IsTwoComponent component) :
    component.map (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤
      Subgroup.centralizer (normalTwo : Set G) := by
  let normalizer := Subgroup.normalizer (twoSubgroup : Set G)
  let ambientComponent := component.map normalizer.subtype
  have hcomponentLe : ambientComponent ≤ normalizer := Subgroup.map_subtype_le component
  have hlocalComponent : TwoComponents.IsTwoComponent (ambientComponent.subgroupOf normalizer) := by
    change TwoComponents.IsTwoComponent ((component.map normalizer.subtype).comap normalizer.subtype)
    rw [Subgroup.comap_map_eq_self_of_injective normalizer.subtype_injective]
    exact hcomponent
  have hcentralizesTwo := TwoComponentCentralizers.le_ambient_centralizer ambientComponent
    twoSubgroup normalizer hcomponentLe Subgroup.le_normalizer le_rfl hlocalComponent htwo
  let localNormalTwo := normalTwo.subgroupOf normalizer
  have hcentralizesLocal := TwoComponentCentralizers.le_centralizer_normal_two component
    localNormalTwo hcomponent hnormalTwo.comap_subtype
  let action : G →* MulAut normalTwo := MulAut.conjNormal
  let leftAction := action.comp (normalizer.subtype.comp component.subtype)
  let rightAction := action.comp twoSubgroup.subtype
  have hcommutes : ∀ left : component, ∀ right : twoSubgroup,
      Commute (leftAction left) (rightAction right) := by
    intro left right
    have hmem : left.val.val ∈ ambientComponent :=
      Subgroup.mem_map_of_mem normalizer.subtype left.property
    have hcommutation := Subgroup.mem_centralizer_iff.mp (hcentralizesTwo hmem)
      right.val right.property
    have hambient : Commute left.val.val right.val := hcommutation.symm
    exact hambient.map action
  have hfixed : ∀ left : component, ∀ member : normalTwo,
      (∀ right : twoSubgroup, rightAction right member = member) → leftAction left member = member := by
    intro left member hfixedMember
    have hmemberNormalizer : member.val ∈ normalizer := by
      apply Subgroup.centralizer_le_normalizer (twoSubgroup : Set G)
      apply Subgroup.mem_centralizer_iff.mpr
      intro right hright
      have hvalue := congrArg Subtype.val (hfixedMember (⟨right, hright⟩ : twoSubgroup))
      change right * member.val * right⁻¹ = member.val at hvalue
      calc
        right * member.val = (right * member.val * right⁻¹) * right := by group
        _ = member.val * right := by rw [hvalue]
    have hlocalMem : (⟨member.val, hmemberNormalizer⟩ : normalizer) ∈ localNormalTwo := member.property
    have hlocalCommutes := Subgroup.mem_centralizer_iff.mp
      (hcentralizesLocal left.property) (⟨member.val, hmemberNormalizer⟩ : normalizer) hlocalMem
    have hcommutation : member.val * left.val.val = left.val.val * member.val :=
      congrArg Subtype.val hlocalCommutes
    apply Subtype.ext
    change left.val.val * member.val * left.val.val⁻¹ = member.val
    rw [← hcommutation]
    group
  let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent⟩
  have hactionIdentity := PerfectCommutingActions.action_eq_one 2 hnormalTwo htwo
    leftAction rightAction hcommutes hfixed
  intro element hmem
  obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmem
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hvalue := congrArg (fun homomorphism : component →* MulAut normalTwo =>
      ((homomorphism (⟨lift, hlift⟩ : component)) (⟨member, hmember⟩ : normalTwo)).val)
    hactionIdentity
  change lift.val * member * lift.val⁻¹ = member at hvalue
  calc
    member * lift.val = (lift.val * member * lift.val⁻¹) * lift.val := by rw [hvalue]
    _ = lift.val * member := by group

theorem bad_le_centralizer {G : Type*} [Group G] [Finite G]
    (twoSubgroup normalTwo : Subgroup G) (htwo : IsPGroup 2 twoSubgroup)
    [normalTwo.Normal] (hnormalTwo : IsPGroup 2 normalTwo) :
    (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
        (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤
      Subgroup.centralizer (normalTwo : Set G) := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro component hbad
  exact Subgroup.map_le_iff_le_comap.mp
    (component_le_centralizer twoSubgroup normalTwo htwo hnormalTwo component hbad.1)

end CFSG.ComponentClassification.LocalAmbientTwoCentralizers
