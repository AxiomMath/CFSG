module

public import CFSG.LocalAnalysis.ComponentClassification.OddKernelNormalizers
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelBadImage
public import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment
public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoBInclusion

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OddKernelBObstruction

theorem exists_bad_component {G H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) [Group.IsSolvable quotient.ker]
    (hquotientB : CentralTwoBInclusion.Property H)
    (twoSubgroup : Subgroup G) (hne : twoSubgroup ≠ ⊥) (htwo : IsPGroup 2 twoSubgroup)
    (hfailure : ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
      (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤ TwoComponents.badSubgroup G) :
    ∃ component : Subgroup (Subgroup.normalizer (twoSubgroup : Set G)),
      TwoComponents.IsTwoComponent component ∧ ¬ IsQuasisimple component ∧
        ¬ component.map (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤
          TwoComponents.badSubgroup G ∧
        IsQuasisimple ((component.map (Subgroup.normalizer (twoSubgroup : Set G)).subtype).map
          quotient) ∧
        ¬ quotient.ker.subgroupOf
          (component.map (Subgroup.normalizer (twoSubgroup : Set G)).subtype) ≤
            Subgroup.center (component.map (Subgroup.normalizer (twoSubgroup : Set G)).subtype) := by
  classical
  let normalizer := Subgroup.normalizer (twoSubgroup : Set G)
  have hexists : ∃ component : Subgroup normalizer,
      TwoComponents.IsTwoComponent component ∧ ¬ IsQuasisimple component ∧
        ¬ component.map normalizer.subtype ≤ TwoComponents.badSubgroup G := by
    by_contra hnone
    apply hfailure
    apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro component hbad
    apply Subgroup.map_le_iff_le_comap.mp
    by_contra hnotContained
    exact hnone ⟨component, hbad.1, hbad.2, hnotContained⟩
  obtain ⟨component, hcomponent, hnotQuasisimple, hnotContained⟩ := hexists
  let ambientComponent := component.map normalizer.subtype
  let targetTwo := twoSubgroup.map quotient
  let targetNormalizer := Subgroup.normalizer (targetTwo : Set H)
  have hnormalizerImage : normalizer.map quotient = targetNormalizer :=
    OddKernelNormalizers.image quotient hsurjective hoddKernel twoSubgroup htwo
  let restriction : normalizer →* targetNormalizer :=
    (quotient.domRestrict normalizer).codRestrict targetNormalizer fun element =>
      hnormalizerImage ▸ Subgroup.mem_map_of_mem quotient element.property
  have hrestrictionSurjective : Function.Surjective restriction := by
    intro element
    have hmem : element.val ∈ normalizer.map quotient := hnormalizerImage.symm ▸ element.property
    obtain ⟨lift, hlift, hvalue⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨lift, hlift⟩, Subtype.ext hvalue⟩
  have hrestrictionKernel : restriction.ker = (quotient.domRestrict normalizer).ker := by
    ext element
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hrestrictionOdd : Odd (Nat.card restriction.ker) := by
    rw [hrestrictionKernel]
    exact OddKernel.odd_card_restriction_kernel quotient hoddKernel normalizer
  have htargetNe : targetTwo ≠ ⊥ := by
    intro hbot
    have hle := (Subgroup.map_eq_bot_iff twoSubgroup).mp hbot
    have hinjective := OddKernel.image_injective_on_two quotient hoddKernel twoSubgroup htwo
    apply hne
    apply le_antisymm _ bot_le
    intro element hmem
    apply Subgroup.mem_bot.mpr
    have heq : (⟨element, hmem⟩ : twoSubgroup) = 1 := hinjective (by
      change quotient element = quotient 1
      rw [map_one]
      exact MonoidHom.mem_ker.mp (hle hmem))
    exact congrArg Subtype.val heq
  have hlocalImageComponent := OddKernelTwoComponents.image restriction hrestrictionSurjective
    hrestrictionOdd component hcomponent
  have himageQuasisimple : IsQuasisimple (component.map restriction) := by
    by_contra hnotQuasisimpleImage
    have hbadLocal : component.map restriction ≤ TwoComponents.badSubgroup targetNormalizer :=
      le_sSup ⟨hlocalImageComponent, hnotQuasisimpleImage⟩
    have hambientImage : ambientComponent.map quotient =
        (component.map restriction).map targetNormalizer.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    have hbadImage : ambientComponent.map quotient ≤ (TwoComponents.badSubgroup G).map quotient := by
      rw [hambientImage]
      exact (Subgroup.map_mono hbadLocal).trans
        ((hquotientB targetTwo htargetNe (htwo.map quotient)).trans
          (OddKernelBadImage.lower_image quotient hsurjective hoddKernel))
    let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent⟩
    let : Group.IsPerfect ambientComponent := Group.IsPerfect.map normalizer.subtype
    let : (TwoComponents.badSubgroup G).Characteristic := BadComponents.characteristic G
    exact hnotContained (SolvableKernelContainment.perfect_containment quotient ambientComponent
      (TwoComponents.badSubgroup G) hbadImage)
  have hambientQuasisimple : IsQuasisimple (ambientComponent.map quotient) := by
    have heq : ambientComponent.map quotient =
        (component.map restriction).map targetNormalizer.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [heq]
    exact Components.quasisimple_of_equiv
      ((component.map restriction).equivMapOfInjective targetNormalizer.subtype
        targetNormalizer.subtype_injective).symm himageQuasisimple
  have hnotCentral : ¬ quotient.ker.subgroupOf ambientComponent ≤ Subgroup.center ambientComponent := by
    intro hcentral
    let image := ambientComponent.map quotient
    let componentRestriction : ambientComponent →* image :=
      (quotient.domRestrict ambientComponent).codRestrict image
        fun element => Subgroup.mem_map_of_mem quotient element.property
    have hcomponentSurjective : Function.Surjective componentRestriction := by
      intro element
      obtain ⟨lift, hlift, hvalue⟩ := Subgroup.mem_map.mp element.property
      exact ⟨⟨lift, hlift⟩, Subtype.ext hvalue⟩
    have hcentralKernel : componentRestriction.ker ≤ Subgroup.center ambientComponent := by
      intro element hmem
      exact hcentral (congrArg Subtype.val (MonoidHom.mem_ker.mp hmem))
    let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent⟩
    let : Group.IsPerfect ambientComponent := Group.IsPerfect.map normalizer.subtype
    have hquasisimple := CentralExtensions.quasisimple_of_surjective hambientQuasisimple
      componentRestriction hcomponentSurjective hcentralKernel
    exact hnotQuasisimple (Components.quasisimple_of_equiv
      (component.equivMapOfInjective normalizer.subtype normalizer.subtype_injective) hquasisimple)
  exact ⟨component, hcomponent, hnotQuasisimple, hnotContained, hambientQuasisimple, hnotCentral⟩

theorem inclusion_of_central_odd_kernel {G H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker))
    (hcentralKernel : quotient.ker ≤ Subgroup.center G)
    (hquotientB : CentralTwoBInclusion.Property H) : CentralTwoBInclusion.Property G := by
  let : IsMulCommutative quotient.ker := ⟨⟨by
    intro left right
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcentralKernel left.property) right.val).symm⟩⟩
  let : Group.IsSolvable quotient.ker := Group.isSolvable_of_comm fun left right =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hcentralKernel left.property) right.val).symm
  intro twoSubgroup hne htwo
  by_contra hfailure
  obtain ⟨component, _, _, _, _, hnotCentral⟩ :=
    exists_bad_component quotient hsurjective hoddKernel hquotientB twoSubgroup hne htwo hfailure
  apply hnotCentral
  intro element hmem
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact Subtype.ext (Subgroup.mem_center_iff.mp (hcentralKernel hmem) other.val)

end CFSG.ComponentClassification.OddKernelBObstruction
