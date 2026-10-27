module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponents

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoComponentCentralizers

theorem oddCore_inf_two_eq_bot {G : Type*} [Group G] [Finite G]
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup) :
    componentClassificationOddCore G ⊓ twoSubgroup = ⊥ := by
  let intersection := componentClassificationOddCore G ⊓ twoSubgroup
  have hintersectionTwo : IsPGroup 2 intersection :=
    htwo.of_injective (Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective inf_le_right)
  obtain ⟨exponent, hcard⟩ := hintersectionTwo.exists_card_eq
  have hodd : Odd (Nat.card intersection) := (OddCore.odd_card G).of_dvd_nat
    (Subgroup.card_dvd_of_le inf_le_left)
  have hcardOne : Nat.card intersection = 1 := by
    apply Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_left.pow_left exponent)
    · rw [hcard]
    · exact dvd_refl _
  exact Subgroup.card_eq_one.mp hcardOne

theorem commutes_with_normal_two {G : Type*} [Group G] [Finite G]
    (component twoSubgroup : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component)
    [twoSubgroup.Normal] (htwo : IsPGroup 2 twoSubgroup) :
    ⁅component, twoSubgroup⁆ = ⊥ := by
  let quotient := QuotientGroup.mk' (componentClassificationOddCore G)
  let image := twoSubgroup.map quotient
  let : image.Normal := Subgroup.Normal.map inferInstance quotient
    (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent image := (htwo.map quotient).isNilpotent
  have himageCommutator : ⁅component.map quotient, image⁆ = ⊥ :=
    LocalComponents.commutes_with_solvable_subnormal _ _ hcomponent.2.1
      (Components.chain_of_mathlib_subnormal
        (Subgroup.IsSubnormal.step image ⊤ le_top Subgroup.IsSubnormal.top inferInstance))
  have hmap : (⁅component, twoSubgroup⁆).map quotient = ⊥ := by
    rw [Subgroup.map_commutator]
    exact himageCommutator
  have hcore : ⁅component, twoSubgroup⁆ ≤ componentClassificationOddCore G := by
    have hkernel := (Subgroup.map_eq_bot_iff _).mp hmap
    simpa only [quotient, QuotientGroup.ker_mk'] using hkernel
  apply le_antisymm _ bot_le
  calc
    ⁅component, twoSubgroup⁆ ≤ componentClassificationOddCore G ⊓ twoSubgroup :=
      le_inf hcore (Subgroup.commutator_le_right _ _)
    _ = ⊥ := oddCore_inf_two_eq_bot twoSubgroup htwo

theorem le_centralizer_normal_two {G : Type*} [Group G] [Finite G]
    (component twoSubgroup : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component)
    [twoSubgroup.Normal] (htwo : IsPGroup 2 twoSubgroup) :
    component ≤ Subgroup.centralizer (twoSubgroup : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (commutes_with_normal_two component twoSubgroup hcomponent htwo)

theorem le_ambient_centralizer {G : Type*} [Group G] [Finite G]
    (component twoSubgroup overgroup : Subgroup G) (hcomponentLe : component ≤ overgroup)
    (htwoLe : twoSubgroup ≤ overgroup)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (twoSubgroup : Set G))
    (hcomponent : TwoComponents.IsTwoComponent (component.subgroupOf overgroup))
    (htwo : IsPGroup 2 twoSubgroup) :
    component ≤ Subgroup.centralizer (twoSubgroup : Set G) := by
  let : (twoSubgroup.subgroupOf overgroup).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf, inf_eq_left.mpr htwoLe]
    exact hnormalizer
  have hlocal := le_centralizer_normal_two (component.subgroupOf overgroup)
    (twoSubgroup.subgroupOf overgroup) hcomponent (htwo.comap_subtype)
  intro element hmem
  have hcentralizer := hlocal (show (⟨element, hcomponentLe hmem⟩ : overgroup) ∈
    component.subgroupOf overgroup from hmem)
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hcommutes := Subgroup.mem_centralizer_iff.mp hcentralizer
    (⟨member, htwoLe hmember⟩ : overgroup) hmember
  exact congrArg Subtype.val hcommutes

end CFSG.ComponentClassification.TwoComponentCentralizers
