module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectCommutingActions
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

open CFSG.Open

namespace CFSG.ComponentClassification.InvolutionLayer

theorem involution_square {G : Type*} [Group G] (element : G) (horder : orderOf element = 2) :
    element * element = 1 := by
  have hpower := pow_orderOf_eq_one element
  rwa [horder, pow_two] at hpower

theorem component_centralizes_normal_two {G : Type*} [Group G] [Finite G]
    (element : G) (horder : orderOf element = 2)
    (normalTwo : Subgroup G) [normalTwo.Normal] (htwo : IsPGroup 2 normalTwo)
    (component : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hcomponent : IsComponentOf component ⊤) :
    component.map (Subgroup.centralizer ({element} : Set G)).subtype ≤
      Subgroup.centralizer (normalTwo : Set G) := by
  let centralizer := Subgroup.centralizer ({element} : Set G)
  let localTwo := normalTwo.subgroupOf centralizer
  let : Group.IsNilpotent localTwo := (htwo.comap_subtype).isNilpotent
  have hlocalCommutes := LocalComponents.commutes_with_solvable_subnormal component localTwo
    hcomponent (Components.chain_of_mathlib_subnormal
      (inferInstance : localTwo.Normal).isSubnormal)
  let cyclic := Subgroup.zpowers element
  have hcyclic : IsPGroup 2 cyclic := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, horder]; rfl)
  let action : G →* MulAut normalTwo := MulAut.conjNormal
  let leftAction : component →* MulAut normalTwo :=
    action.comp (centralizer.subtype.comp component.subtype)
  let rightAction : cyclic →* MulAut normalTwo := action.comp cyclic.subtype
  have hcommutes : ∀ actor : component, ∀ member : cyclic,
      Commute (leftAction actor) (rightAction member) := by
    intro actor member
    have hactor : actor.val.val * element = element * actor.val.val :=
      Subgroup.mem_centralizer_singleton_iff.mp actor.val.property
    have hcyclicLe : cyclic ≤ Subgroup.centralizer ({actor.val.val} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hactor.symm)
    have heq := Subgroup.mem_centralizer_singleton_iff.mp (hcyclicLe member.property)
    exact (show Commute actor.val.val member.val from heq.symm).map action
  have hfixed : ∀ actor : component, ∀ member : normalTwo,
      (∀ cyclicMember : cyclic, rightAction cyclicMember member = member) →
        leftAction actor member = member := by
    intro actor member hmember
    have heq := congrArg Subtype.val (hmember (⟨element, Subgroup.mem_zpowers element⟩ : cyclic))
    change element * member.val * element⁻¹ = member.val at heq
    have hcentralizer : member.val ∈ centralizer := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      calc
        member.val * element = (element * member.val * element⁻¹) * element := by rw [heq]
        _ = element * member.val := by group
    have hlocal : (⟨member.val, hcentralizer⟩ : centralizer) ∈ localTwo := member.property
    have hcommutation := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hlocalCommutes actor.property)
        (⟨member.val, hcentralizer⟩ : centralizer) hlocal)
    change member.val * actor.val.val = actor.val.val * member.val at hcommutation
    apply Subtype.ext
    change actor.val.val * member.val * actor.val.val⁻¹ = member.val
    rw [← hcommutation]
    group
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  have htrivial := PerfectCommutingActions.action_eq_one 2 htwo hcyclic
    leftAction rightAction hcommutes hfixed
  intro actor hactor
  obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hactor
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have heq := congrArg (fun homomorphism : component →* MulAut normalTwo =>
    ((homomorphism (⟨lift, hlift⟩ : component)) (⟨member, hmember⟩ : normalTwo)).val) htrivial
  change lift.val * member * lift.val⁻¹ = member at heq
  calc
    member * lift.val = (lift.val * member * lift.val⁻¹) * lift.val := by rw [heq]
    _ = lift.val * member := by group

theorem component_enters_layer {G : Type*} [Group G] [Finite G]
    (hcorefree : componentClassificationOddCore G = ⊥) (element : G)
    (horder : orderOf element = 2)
    (houter : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component)))
    (localComponent : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hlocal : IsComponentOf localComponent ⊤) :
    localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype ≤ Layer.subgroup G := by
  let centralizer := Subgroup.centralizer ({element} : Set G)
  let layer := Layer.subgroup G
  let : layer.Normal := Layer.normal G
  let localLayer := layer.subgroupOf centralizer
  let : localLayer.Normal := inferInstance
  rcases LocalComponents.normal_contains_or_commutes localComponent localLayer hlocal with
    hcontained | hcommutes
  · intro member hmember
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
    exact hcontained hlift
  · let image := localComponent.map centralizer.subtype
    let : Group.IsPerfect image := ⟨(Components.quasisimple_of_equiv
      (localComponent.equivMapOfInjective centralizer.subtype centralizer.subtype_injective).symm
      hlocal.2.2).1⟩
    have hfixed : ⁅image, layer ⊓ centralizer⁆ = ⊥ := by
      have hmap := congrArg (Subgroup.map centralizer.subtype) hcommutes
      change ⁅localComponent, layer.subgroupOf centralizer⁆.map centralizer.subtype =
        (⊥ : Subgroup centralizer).map centralizer.subtype at hmap
      simpa only [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
        Subgroup.map_bot] using hmap
    let twoCore := PrimeCore.subgroup 2 G
    let : twoCore.Normal := PrimeCore.normal 2 G
    have hcentralizesFitting : ⁅image, Fitting.subgroup G⁆ = ⊥ := by
      rw [PrimeCore.fitting_eq_two_of_odd_corefree hcorefree]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (component_centralizes_normal_two element horder twoCore (PrimeCore.isPGroup 2 G)
          localComponent hlocal)
    have hsquare : element * element = 1 := involution_square element horder
    apply GeneralizedFitting.perfect_normalizer_enters_layer image hcentralizesFitting _ houter
    intro component hcomponent
    exact GeneralizedFitting.involution_fixed_layer_centralizer_normalizes image element hsquare
      (Subgroup.map_subtype_le _) hcentralizesFitting hfixed component hcomponent

end CFSG.ComponentClassification.InvolutionLayer
