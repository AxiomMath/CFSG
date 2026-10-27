module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ComponentClassification.Components
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

open CFSG.Open

namespace CFSG.ComponentClassification.LocalComponents

theorem of_overgroup {G : Type*} [Group G] {component overgroup : Subgroup G}
    (hcomponent : IsComponentOf component ⊤) (hle : component ≤ overgroup) :
    IsComponentOf (component.subgroupOf overgroup) ⊤ := by
  refine ⟨le_top, ?_, Components.quasisimple_of_equiv
    (Subgroup.subgroupOfEquivOfLe hle) hcomponent.2.2⟩
  apply Components.chain_of_mathlib_subnormal
  exact (Components.mathlib_subnormal_of_chain hcomponent.2.1
    Subgroup.IsSubnormal.top).subgroupOf

theorem image {G H : Type*} [Group G] [Group H] {component : Subgroup G}
    (hcomponent : IsComponentOf component ⊤) (quotient : G →* H)
    (hsurjective : Function.Surjective quotient) (hnotKilled : ¬ component ≤ quotient.ker) :
    IsComponentOf (component.map quotient) ⊤ := by
  let image := component.map quotient
  let restriction : component →* image :=
    (quotient.domRestrict component).codRestrict image
      fun element => Subgroup.mem_map_of_mem quotient element.property
  have hrestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hmem, hlift⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hlift⟩
  have hkernel : restriction.ker ≠ ⊤ := by
    intro htop
    apply hnotKilled
    intro element hmem
    have hone : restriction ⟨element, hmem⟩ = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [htop]
      exact Subgroup.mem_top _
    exact congrArg Subtype.val hone
  have hquasisimple := Quasisimple.central_quotient hcomponent.2.2 restriction.ker
    (Quasisimple.normal_le_center_of_ne_top hcomponent.2.2 restriction.ker hkernel)
  refine ⟨le_top, ?_, Components.quasisimple_of_equiv
    (QuotientGroup.liftEquiv restriction.ker hrestriction rfl).symm hquasisimple⟩
  apply Components.chain_of_mathlib_subnormal
  exact (Components.mathlib_subnormal_of_chain hcomponent.2.1
    Subgroup.IsSubnormal.top).map hsurjective

theorem normal_contains_or_commutes {G : Type*} [Group G] [Finite G]
    (component normalSubgroup : Subgroup G) (hcomponent : IsComponentOf component ⊤)
    [normalSubgroup.Normal] :
    component ≤ normalSubgroup ∨ ⁅component, normalSubgroup⁆ = ⊥ := by
  induction hcard : Nat.card G using Nat.strong_induction_on generalizing G with
  | h cardinal hinduction =>
      have hsubnormal := Components.mathlib_subnormal_of_chain hcomponent.2.1
        Subgroup.IsSubnormal.top
      rcases hsubnormal.lt_normal with htop | ⟨overgroup, hnormal, hle, hproper⟩
      · have hquasisimple : IsQuasisimple G := by
          have hquasisimple := hcomponent.2.2
          rw [htop] at hquasisimple
          exact Components.quasisimple_of_equiv Subgroup.topEquiv.symm hquasisimple
        rcases Quasisimple.normal_le_center_or_eq_top hquasisimple normalSubgroup with
          hcentral | hnormalTop
        · right
          rw [htop]
          exact Subgroup.commutator_top_left_eq_bot_iff_le_center.mpr hcentral
        · left
          rw [hnormalTop]
          exact le_top
      · let : overgroup.Normal := hnormal
        have hsmaller : Nat.card overgroup < cardinal := by
          have hleCard := overgroup.card_le_card_group
          have hneCard : Nat.card overgroup ≠ Nat.card G := fun heq =>
            (ne_of_lt hproper) (overgroup.card_eq_iff_eq_top.mp heq)
          omega
        have hlocal := hinduction (Nat.card overgroup) hsmaller
          (component.subgroupOf overgroup) (normalSubgroup.subgroupOf overgroup)
          (of_overgroup hcomponent hle) rfl
        rcases hlocal with hcontained | hcommute
        · left
          intro element hmem
          exact hcontained (show (⟨element, hle hmem⟩ : overgroup) ∈
            component.subgroupOf overgroup from hmem)
        · right
          have hintersection : ⁅component, normalSubgroup ⊓ overgroup⁆ = ⊥ := by
            have hmap := congrArg (Subgroup.map overgroup.subtype) hcommute
            simpa only [Subgroup.map_commutator,
              Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.subgroupOf_map_subtype,
              Subgroup.map_bot] using hmap
          have hdisplacement : ⁅component, normalSubgroup⁆ ≤ normalSubgroup ⊓ overgroup := by
            apply le_inf
            · exact Subgroup.commutator_le_right component normalSubgroup
            · exact (Subgroup.commutator_mono hle le_rfl).trans
                (Subgroup.commutator_le_left overgroup normalSubgroup)
          have hdouble : ⁅⁅component, normalSubgroup⁆, component⁆ = ⊥ := by
            apply le_antisymm _ bot_le
            have hbound := Subgroup.commutator_mono hdisplacement
              (le_rfl : component ≤ component)
            rw [Subgroup.commutator_comm (normalSubgroup ⊓ overgroup) component,
              hintersection] at hbound
            exact hbound
          let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
          exact Quasisimple.perfect_double_commutator component normalSubgroup hdouble

theorem subnormal_contains_or_commutes {G : Type*} [Group G] [Finite G]
    (component subgroup : Subgroup G) (hcomponent : IsComponentOf component ⊤)
    (hsubnormal : IsSubnormal subgroup ⊤) :
    component ≤ subgroup ∨ ⁅component, subgroup⁆ = ⊥ := by
  have hchain := Components.mathlib_subnormal_of_chain hsubnormal Subgroup.IsSubnormal.top
  clear hsubnormal
  induction hchain with
  | top => exact Or.inl le_top
  | step lower upper hle hsubnormal hnormal hinduction =>
      rcases hinduction with hcontained | hcommutes
      · let : (lower.subgroupOf upper).Normal := hnormal
        have hlocal := normal_contains_or_commutes (component.subgroupOf upper)
          (lower.subgroupOf upper) (of_overgroup hcomponent hcontained)
        rcases hlocal with hlocalContained | hlocalCommutes
        · left
          intro element hmem
          exact hlocalContained (show (⟨element, hcontained hmem⟩ : upper) ∈
            component.subgroupOf upper from hmem)
        · right
          have hmap := congrArg (Subgroup.map upper.subtype) hlocalCommutes
          simpa only [Subgroup.map_commutator,
            Subgroup.map_subgroupOf_eq_of_le hcontained,
            Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using hmap
      · right
        apply le_antisymm _ bot_le
        have hbound := Subgroup.commutator_mono (le_rfl : component ≤ component) hle
        rw [hcommutes] at hbound
        exact hbound

theorem eq_of_le {G : Type*} [Group G] (first second : Subgroup G)
    (hfirst : IsComponentOf first ⊤) (hsecond : IsComponentOf second ⊤)
    (hle : first ≤ second) : first = second := by
  have hlocal := of_overgroup hfirst hle
  let : Group.IsPerfect (first.subgroupOf second) := ⟨hlocal.2.2.1⟩
  rcases Quasisimple.perfect_subnormal_eq_bot_or_eq_top hsecond.2.2
      (first.subgroupOf second) hlocal.2.1 with hbot | htop
  · have hfirstBot : first = ⊥ := by
      have hmap := congrArg (Subgroup.map second.subtype) hbot
      simpa only [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using hmap
    let : Nontrivial first := Quasisimple.nontrivial hfirst.2.2
    exact ((first.nontrivial_iff_ne_bot.mp inferInstance) hfirstBot).elim
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

theorem commute_of_ne {G : Type*} [Group G] [Finite G] (first second : Subgroup G)
    (hfirst : IsComponentOf first ⊤) (hsecond : IsComponentOf second ⊤)
    (hne : first ≠ second) : ⁅first, second⁆ = ⊥ := by
  rcases subnormal_contains_or_commutes first second hfirst hsecond.2.1 with hle | hcommutes
  · exact (hne (eq_of_le first second hfirst hsecond hle)).elim
  · exact hcommutes

theorem commutes_with_solvable_subnormal {G : Type*} [Group G] [Finite G]
    (component solvableSubgroup : Subgroup G) (hcomponent : IsComponentOf component ⊤)
    (hsubnormal : IsSubnormal solvableSubgroup ⊤) [Group.IsSolvable solvableSubgroup] :
    ⁅component, solvableSubgroup⁆ = ⊥ := by
  rcases subnormal_contains_or_commutes component solvableSubgroup hcomponent hsubnormal with
    hcontained | hcommutes
  · let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
    let : Nontrivial component := Quasisimple.nontrivial hcomponent.2.2
    let : Group.IsSolvable component := Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hcontained)
    exact (Group.IsPerfect.not_isSolvable component inferInstance).elim
  · exact hcommutes

theorem equiv_iff {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H)
    (component : Subgroup G) :
    IsComponentOf (component.map equivalence.toMonoidHom) ⊤ ↔
      IsComponentOf component ⊤ := by
  constructor
  · intro hcomponent
    have hsubnormal := Components.mathlib_subnormal_of_chain hcomponent.2.1
      Subgroup.IsSubnormal.top
    have hmap : (component.map equivalence.toMonoidHom).map equivalence.symm.toMonoidHom =
        component := by
      ext element
      constructor
      · rintro ⟨image, ⟨lift, hmem, rfl⟩, rfl⟩
        change equivalence.symm (equivalence lift) ∈ component
        rw [equivalence.symm_apply_apply]
        exact hmem
      · intro hmem
        exact ⟨equivalence element, ⟨element, hmem, rfl⟩,
          equivalence.symm_apply_apply element⟩
    refine ⟨le_top, ?_, Components.quasisimple_of_equiv
      (component.equivMapOfInjective equivalence.toMonoidHom equivalence.injective)
      hcomponent.2.2⟩
    apply Components.chain_of_mathlib_subnormal
    have hchain := hsubnormal.map (f := equivalence.symm.toMonoidHom)
      equivalence.symm.surjective
    rw [hmap] at hchain
    exact hchain
  · intro hcomponent
    refine ⟨le_top, ?_, Components.quasisimple_of_equiv
      (component.equivMapOfInjective equivalence.toMonoidHom equivalence.injective).symm
      hcomponent.2.2⟩
    apply Components.chain_of_mathlib_subnormal
    exact (Components.mathlib_subnormal_of_chain hcomponent.2.1
      Subgroup.IsSubnormal.top).map equivalence.surjective

theorem of_subnormal_subgroup {G : Type*} [Group G] (subgroup : Subgroup G)
    (hsubnormal : IsSubnormal subgroup ⊤) (component : Subgroup subgroup)
    (hcomponent : IsComponentOf component ⊤) :
    IsComponentOf (component.map subgroup.subtype) ⊤ := by
  refine ⟨le_top, ?_, Components.quasisimple_of_equiv
    (component.equivMapOfInjective subgroup.subtype subgroup.subtype_injective).symm
    hcomponent.2.2⟩
  apply Components.chain_of_mathlib_subnormal
  exact (Components.mathlib_subnormal_of_chain hcomponent.2.1 Subgroup.IsSubnormal.top).trans'
    (Components.mathlib_subnormal_of_chain hsubnormal Subgroup.IsSubnormal.top)

end CFSG.ComponentClassification.LocalComponents
