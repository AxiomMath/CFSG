module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoResidual
public import CFSG.LocalAnalysis.ComponentClassification.OddKernel
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoKernelComponents

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OddKernelNormalizers

theorem normalizer_le_sup_of_odd_relative_index {G : Type*} [Group G] [Finite G]
    (twoSubgroup overgroup : Subgroup G) (hle : twoSubgroup ≤ overgroup)
    (htwo : IsPGroup 2 twoSubgroup) (hoddIndex : Odd (twoSubgroup.subgroupOf overgroup).index) :
    Subgroup.normalizer (overgroup : Set G) ≤
      Subgroup.normalizer (twoSubgroup : Set G) ⊔ overgroup := by
  let normalizer := Subgroup.normalizer (overgroup : Set G)
  have hovergroupLe : overgroup ≤ normalizer := Subgroup.le_normalizer
  have htwoLe : twoSubgroup ≤ normalizer := hle.trans hovergroupLe
  let equivalence := (Subgroup.subgroupOfEquivOfLe hovergroupLe).symm
  let sylow : Sylow 2 overgroup :=
    (htwo.comap_subtype).toSylow hoddIndex.not_two_dvd_nat
  have hequivalenceSurjective : Function.Surjective equivalence.toMonoidHom := by
    intro element
    exact ⟨equivalence.symm element, equivalence.apply_symm_apply element⟩
  let localSylow : Sylow 2 (overgroup.subgroupOf normalizer) :=
    sylow.mapSurjective (f := equivalence.toMonoidHom) hequivalenceSurjective
  have hsylow : (sylow : Subgroup overgroup) = twoSubgroup.subgroupOf overgroup :=
    IsPGroup.toSylow_coe _ _
  have hlocalSylow : (localSylow : Subgroup (overgroup.subgroupOf normalizer)).map
      (overgroup.subgroupOf normalizer).subtype = twoSubgroup.subgroupOf normalizer := by
    dsimp only [localSylow]
    rw [Sylow.coe_mapSurjective, hsylow]
    ext element
    constructor
    · rintro ⟨member, ⟨lift, hlift, rfl⟩, rfl⟩
      exact hlift
    · intro hmem
      exact ⟨⟨element, hle hmem⟩,
        ⟨⟨element.val, hle hmem⟩, hmem, rfl⟩, rfl⟩
  have hfrattini := localSylow.normalizer_sup_eq_top
  rw [hlocalSylow, ← Subgroup.subgroupOf_normalizer_eq htwoLe] at hfrattini
  intro element hmem
  have htop : (⟨element, hmem⟩ : normalizer) ∈
      (Subgroup.normalizer (twoSubgroup : Set G)).subgroupOf normalizer ⊔
        overgroup.subgroupOf normalizer := by rw [hfrattini]; exact Subgroup.mem_top _
  obtain ⟨normalizing, hnormalizing, member, hmember, hvalue⟩ :=
    Subgroup.mem_sup_of_normal_right.mp htop
  have heq : normalizing.val * member.val = element := congrArg Subtype.val hvalue
  rw [← heq]
  exact Subgroup.mul_mem_sup hnormalizing hmember

theorem image {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker))
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup) :
    (Subgroup.normalizer (twoSubgroup : Set G)).map quotient =
      Subgroup.normalizer (twoSubgroup.map quotient : Set H) := by
  apply le_antisymm (Subgroup.le_normalizer_map quotient)
  intro element hmem
  obtain ⟨lift, hvalue⟩ := hsurjective element
  let image := twoSubgroup.map quotient
  let preimage := image.comap quotient
  have htwoLe : twoSubgroup ≤ preimage := Subgroup.le_comap_map quotient _
  let restriction : preimage →* image :=
    (quotient.domRestrict preimage).codRestrict image fun member => member.property
  have hsurjectiveRestriction : Function.Surjective restriction := by
    intro member
    obtain ⟨memberLift, hmemberValue⟩ := hsurjective member.val
    have hmember : memberLift ∈ preimage := by
      change quotient memberLift ∈ image
      rw [hmemberValue]
      exact member.property
    exact ⟨⟨memberLift, hmember⟩, Subtype.ext hmemberValue⟩
  have hkernel : restriction.ker = (quotient.domRestrict preimage).ker := by
    ext member
    change restriction member = 1 ↔ quotient member.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hoddRestriction : Odd (Nat.card restriction.ker) := by
    rw [hkernel]
    exact OddKernel.odd_card_restriction_kernel quotient hoddKernel preimage
  have hcovering : Function.Surjective
      (restriction.domRestrict (twoSubgroup.subgroupOf preimage)) := by
    intro member
    obtain ⟨memberLift, hmember, hmemberValue⟩ := Subgroup.mem_map.mp member.property
    exact ⟨⟨⟨memberLift, htwoLe hmember⟩, hmember⟩, Subtype.ext hmemberValue⟩
  have hoddIndex := TwoResidual.odd_index_of_covering restriction hsurjectiveRestriction
    hoddRestriction (twoSubgroup.subgroupOf preimage) hcovering
  have hnormalizes : lift ∈ Subgroup.normalizer (preimage : Set G) := by
    have hcomap := Subgroup.comap_normalizer_eq_of_surjective image hsurjective
    rw [← hcomap]
    change quotient lift ∈ Subgroup.normalizer (image : Set H)
    rwa [hvalue]
  have hproduct := normalizer_le_sup_of_odd_relative_index twoSubgroup preimage htwoLe htwo
    hoddIndex hnormalizes
  have hpreimage : preimage = twoSubgroup ⊔ quotient.ker := Subgroup.comap_map_eq quotient _
  have hnormalizerProduct :
      Subgroup.normalizer (twoSubgroup : Set G) ⊔ preimage =
        Subgroup.normalizer (twoSubgroup : Set G) ⊔ quotient.ker := by
    rw [hpreimage, ← sup_assoc, sup_eq_left.mpr Subgroup.le_normalizer]
  rw [hnormalizerProduct] at hproduct
  obtain ⟨normalizing, hnormalizing, kernelMember, hkernelMember, hsplit⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hproduct
  have himageValue : quotient normalizing = element := by
    rw [← hvalue, ← hsplit, map_mul, MonoidHom.mem_ker.mp hkernelMember, mul_one]
  exact ⟨normalizing, hnormalizing, himageValue⟩

end CFSG.ComponentClassification.OddKernelNormalizers
