module

public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoBInclusion
public import CFSG.LocalAnalysis.ComponentClassification.BadSolvableQuotients

public section

open CFSG.Open

namespace CFSG.ComponentClassification.LocalBNormalGeneration

theorem perfect_normalClosure {G : Type*} [Group G]
    (subgroup : Subgroup G) [Group.IsPerfect subgroup] :
    Group.IsPerfect (Subgroup.normalClosure (subgroup : Set G)) := by
  let normalClosure := Subgroup.normalClosure (subgroup : Set G)
  have hle : subgroup ≤ normalClosure := Subgroup.subset_normalClosure
  let : (⁅normalClosure, normalClosure⁆).Normal := by
    rw [← Subgroup.map_subtype_commutator]
    exact ConjAct.normal_of_characteristic_of_normal
  have hderived : subgroup ≤ ⁅normalClosure, normalClosure⁆ := by
    calc
      subgroup = ⁅subgroup, subgroup⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅normalClosure, normalClosure⁆ := Subgroup.commutator_mono hle hle
  have heq : ⁅normalClosure, normalClosure⁆ = normalClosure :=
    le_antisymm (Subgroup.commutator_le_self _) (Subgroup.normalClosure_le_normal hderived)
  exact Subgroup.isPerfect_iff.mpr heq

theorem component_le_bad_overgroup {G : Type*} [Group G] [Finite G]
    (twoSubgroup overgroup component : Subgroup G)
    (htwoLe : twoSubgroup ≤ overgroup) (hne : twoSubgroup ≠ ⊥)
    (htwo : IsPGroup 2 twoSubgroup)
    (hcomponentNormalizer : component ≤ Subgroup.normalizer (twoSubgroup : Set G))
    (hcomponentOvergroup : component ≤ overgroup)
    (hcomponent : TwoComponents.IsTwoComponent
      (component.subgroupOf (Subgroup.normalizer (twoSubgroup : Set G))))
    (hnotQuasisimple : ¬ IsQuasisimple component)
    (hB : CentralTwoBInclusion.Property overgroup) :
    component ≤ (TwoComponents.badSubgroup overgroup).map overgroup.subtype := by
  let normalizer := Subgroup.normalizer (twoSubgroup : Set G)
  let intersection := normalizer ⊓ overgroup
  have hintersectionLe : component ≤ intersection :=
    le_inf hcomponentNormalizer hcomponentOvergroup
  have hbadIntersection : component ≤
      (TwoComponents.badSubgroup intersection).map intersection.subtype := by
    rw [BadComponents.ambient_description]
    exact le_sSup ⟨hintersectionLe, TwoComponentTransport.restrict_nested component intersection
      normalizer hintersectionLe inf_le_left hcomponent, hnotQuasisimple⟩
  let localTwo := twoSubgroup.subgroupOf overgroup
  let localNormalizer := Subgroup.normalizer (localTwo : Set overgroup)
  have hlocalNe : localTwo ≠ ⊥ := by
    intro hbot
    have hmap := congrArg (Subgroup.map overgroup.subtype) hbot
    rw [Subgroup.map_subgroupOf_eq_of_le htwoLe, Subgroup.map_bot] at hmap
    exact hne hmap
  have hlocalB := hB localTwo hlocalNe htwo.comap_subtype
  have hnormalizerEq : localNormalizer = normalizer.subgroupOf overgroup :=
    (Subgroup.subgroupOf_normalizer_eq htwoLe).symm
  have hnormalizerMap : localNormalizer.map overgroup.subtype = intersection := by
    rw [hnormalizerEq, Subgroup.subgroupOf_map_subtype]
  let equivalence :=
    (localNormalizer.equivMapOfInjective overgroup.subtype overgroup.subtype_injective).trans
      (MulEquiv.subgroupCongr hnormalizerMap)
  have hbadMap : ((TwoComponents.badSubgroup localNormalizer).map localNormalizer.subtype).map
      overgroup.subtype = (TwoComponents.badSubgroup intersection).map intersection.subtype := by
    have hinvariant := BadComponents.equiv_invariant equivalence
    have hcomposite : overgroup.subtype.comp localNormalizer.subtype =
        intersection.subtype.comp equivalence.toMonoidHom := rfl
    rw [Subgroup.map_map, hcomposite, ← Subgroup.map_map, hinvariant]
  have hlocalImage := Subgroup.map_mono (f := overgroup.subtype) hlocalB
  rw [hbadMap] at hlocalImage
  exact hbadIntersection.trans hlocalImage

theorem normalClosure_sup_two_eq_top {G : Type*} [Group G] [Finite G]
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (twoSubgroup component : Subgroup G) (hne : twoSubgroup ≠ ⊥)
    (htwo : IsPGroup 2 twoSubgroup)
    (hcomponentLe : component ≤ Subgroup.normalizer (twoSubgroup : Set G))
    (hcomponent : TwoComponents.IsTwoComponent
      (component.subgroupOf (Subgroup.normalizer (twoSubgroup : Set G))))
    (hnotQuasisimple : ¬ IsQuasisimple component)
    (hnotContained : ¬ component ≤ TwoComponents.badSubgroup G) :
    Subgroup.normalClosure (component : Set G) ⊔ twoSubgroup = ⊤ := by
  classical
  let normalClosure := Subgroup.normalClosure (component : Set G)
  by_contra hproperJoin
  have hcomponentClosure : component ≤ normalClosure := Subgroup.subset_normalClosure
  have hcomponentJoin : component ≤ normalClosure ⊔ twoSubgroup :=
    hcomponentClosure.trans le_sup_left
  have hbadJoin := component_le_bad_overgroup twoSubgroup (normalClosure ⊔ twoSubgroup) component
    le_sup_right hne htwo hcomponentLe hcomponentJoin hcomponent hnotQuasisimple
      (hproper _ hproperJoin)
  have hbadClosure := BadSolvableQuotients.bad_sup_normal_two normalClosure twoSubgroup htwo
  have hclosureSubnormal : IsSubnormal normalClosure ⊤ :=
    Components.chain_of_mathlib_subnormal (Subgroup.IsSubnormal.step normalClosure ⊤ le_top
      Subgroup.IsSubnormal.top inferInstance)
  exact hnotContained (hbadJoin.trans (hbadClosure.trans
    (BadComponentDetection.subnormal_monotone normalClosure hclosureSubnormal)))

theorem normalClosure_eq_derived_of_commutative {G : Type*} [Group G] [Finite G]
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (twoSubgroup component : Subgroup G) (hne : twoSubgroup ≠ ⊥)
    (htwo : IsPGroup 2 twoSubgroup) (hcommutative : IsMulCommutative twoSubgroup)
    (hcomponentLe : component ≤ Subgroup.normalizer (twoSubgroup : Set G))
    (hcomponent : TwoComponents.IsTwoComponent
      (component.subgroupOf (Subgroup.normalizer (twoSubgroup : Set G))))
    (hnotQuasisimple : ¬ IsQuasisimple component)
    (hnotContained : ¬ component ≤ TwoComponents.badSubgroup G) :
    Subgroup.normalClosure (component : Set G) = commutator G := by
  let normalClosure := Subgroup.normalClosure (component : Set G)
  let equivalence := Subgroup.subgroupOfEquivOfLe hcomponentLe
  let : Group.IsPerfect (component.subgroupOf (Subgroup.normalizer (twoSubgroup : Set G))) :=
    ⟨TwoComponents.perfect hcomponent⟩
  let : Group.IsPerfect component :=
    Group.IsPerfect.ofSurjective (f := equivalence.toMonoidHom) equivalence.surjective
  let : Group.IsPerfect normalClosure := perfect_normalClosure component
  have hcover := normalClosure_sup_two_eq_top hproper twoSubgroup component hne htwo
    hcomponentLe hcomponent hnotQuasisimple hnotContained
  apply le_antisymm
  · calc
      normalClosure = ⁅normalClosure, normalClosure⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := rfl
  · exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hcover hcommutative

theorem index_le_card_of_normal_sup {G : Type*} [Group G] [Finite G]
    (normalSubgroup supplement : Subgroup G) [normalSubgroup.Normal]
    (hcover : normalSubgroup ⊔ supplement = ⊤) : normalSubgroup.index ≤ Nat.card supplement := by
  let projection := QuotientGroup.mk' normalSubgroup
  have hnormalImage : normalSubgroup.map projection = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  have hsupplementImage : supplement.map projection = ⊤ := by
    have hmap := congrArg (Subgroup.map projection) hcover
    rw [Subgroup.map_sup, hnormalImage, bot_sup_eq,
      Subgroup.map_top_of_surjective projection (QuotientGroup.mk'_surjective _)] at hmap
    exact hmap
  have hsurjective : Function.Surjective (projection.domRestrict supplement) := by
    intro element
    have hmem : element ∈ supplement.map projection := hsupplementImage ▸ Subgroup.mem_top element
    obtain ⟨lift, hmem, hvalue⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨lift, hmem⟩, hvalue⟩
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_surjective (projection.domRestrict supplement) hsurjective

end CFSG.ComponentClassification.LocalBNormalGeneration
