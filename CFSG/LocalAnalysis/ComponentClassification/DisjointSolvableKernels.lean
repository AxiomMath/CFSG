module

public import CFSG.LocalAnalysis.ComponentClassification.OddKernelBObstruction

public section

open CFSG.Open

namespace CFSG.ComponentClassification.DisjointSolvableKernels

theorem kernel_central_of_quasisimple_image {G H K : Type*}
    [Group G] [Group H] [Group K]
    (first : G →* H) (second : G →* K)
    [Group.IsSolvable first.ker]
    (hsurjective : Function.Surjective second) (hquasisimple : IsQuasisimple K)
    (hdisjoint : first.ker ⊓ second.ker = ⊥) : first.ker ≤ Subgroup.center G := by
  let image := first.ker.map second
  let restriction : first.ker →* image :=
    (second.domRestrict first.ker).codRestrict image fun element =>
      Subgroup.mem_map_of_mem second element.property
  have hrestrictionSurjective : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hmem, hvalue⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hvalue⟩
  let : Group.IsSolvable image := Group.isSolvable_of_surjective hrestrictionSurjective
  let : image.Normal := Subgroup.Normal.map inferInstance second hsurjective
  have hproper : image ≠ ⊤ := by
    intro htop
    have hsurjectiveImage : Function.Surjective image.subtype := by
      intro element
      exact ⟨⟨element, htop ▸ Subgroup.mem_top element⟩, rfl⟩
    let : Group.IsSolvable K := Group.isSolvable_of_surjective hsurjectiveImage
    let : Group.IsPerfect K := ⟨hquasisimple.1⟩
    let : Nontrivial K := Quasisimple.nontrivial hquasisimple
    exact Group.IsPerfect.not_isSolvable K inferInstance
  have hcentral := Quasisimple.normal_le_center_of_ne_top hquasisimple image hproper
  have hmap : (⁅(⊤ : Subgroup G), first.ker⁆).map second = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective second hsurjective]
    exact Subgroup.commutator_top_left_eq_bot_iff_le_center.mpr hcentral
  have hsecond := (Subgroup.map_eq_bot_iff _).mp hmap
  have hfirst := Subgroup.commutator_le_right (⊤ : Subgroup G) first.ker
  have hbot : ⁅(⊤ : Subgroup G), first.ker⁆ = ⊥ :=
    le_antisymm ((le_inf hfirst hsecond).trans (le_of_eq hdisjoint)) bot_le
  exact Subgroup.commutator_top_left_eq_bot_iff_le_center.mp hbot

theorem inclusion {G H K : Type*}
    [Group G] [Finite G] [Group H] [Finite H] [Group K] [Finite K]
    (first : G →* H) (second : G →* K)
    (hfirstSurjective : Function.Surjective first)
    (hsecondSurjective : Function.Surjective second)
    (hfirstOdd : Odd (Nat.card first.ker)) (hsecondOdd : Odd (Nat.card second.ker))
    [Group.IsSolvable first.ker] [Group.IsSolvable second.ker]
    (hdisjoint : first.ker ⊓ second.ker = ⊥)
    (hfirstB : CentralTwoBInclusion.Property H)
    (hsecondB : CentralTwoBInclusion.Property K) : CentralTwoBInclusion.Property G := by
  intro twoSubgroup hne htwo
  by_contra hfailure
  obtain ⟨component, hcomponent, _, hnotContained, _, hnotCentral⟩ :=
    OddKernelBObstruction.exists_bad_component first hfirstSurjective hfirstOdd
      hfirstB twoSubgroup hne htwo hfailure
  let normalizer := Subgroup.normalizer (twoSubgroup : Set G)
  let ambientComponent := component.map normalizer.subtype
  let targetTwo := twoSubgroup.map second
  let targetNormalizer := Subgroup.normalizer (targetTwo : Set K)
  have hnormalizerImage : normalizer.map second = targetNormalizer :=
    OddKernelNormalizers.image second hsecondSurjective hsecondOdd twoSubgroup htwo
  let restriction : normalizer →* targetNormalizer :=
    (second.domRestrict normalizer).codRestrict targetNormalizer fun element =>
      hnormalizerImage ▸ Subgroup.mem_map_of_mem second element.property
  have hrestrictionSurjective : Function.Surjective restriction := by
    intro element
    have hmem : element.val ∈ normalizer.map second := hnormalizerImage.symm ▸ element.property
    obtain ⟨lift, hmem, hvalue⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨lift, hmem⟩, Subtype.ext hvalue⟩
  have hrestrictionKernel : restriction.ker = (second.domRestrict normalizer).ker := by
    ext element
    change restriction element = 1 ↔ second element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hrestrictionOdd : Odd (Nat.card restriction.ker) := by
    rw [hrestrictionKernel]
    exact OddKernel.odd_card_restriction_kernel second hsecondOdd normalizer
  have htargetNe : targetTwo ≠ ⊥ := by
    intro hbot
    have hle := (Subgroup.map_eq_bot_iff twoSubgroup).mp hbot
    have hinjective := OddKernel.image_injective_on_two second hsecondOdd twoSubgroup htwo
    apply hne
    apply le_antisymm _ bot_le
    intro element hmem
    apply Subgroup.mem_bot.mpr
    have heq : (⟨element, hmem⟩ : twoSubgroup) = 1 := hinjective (by
      change second element = second 1
      rw [map_one]
      exact MonoidHom.mem_ker.mp (hle hmem))
    exact congrArg Subtype.val heq
  have himageComponent := OddKernelTwoComponents.image restriction hrestrictionSurjective
    hrestrictionOdd component hcomponent
  have hnotQuasisimple : ¬ IsQuasisimple (component.map restriction) := by
    intro hquasisimple
    apply hnotCentral
    let image := ambientComponent.map second
    let componentRestriction : ambientComponent →* image :=
      (second.domRestrict ambientComponent).codRestrict image fun element =>
        Subgroup.mem_map_of_mem second element.property
    have hcomponentSurjective : Function.Surjective componentRestriction := by
      intro element
      obtain ⟨lift, hmem, hvalue⟩ := Subgroup.mem_map.mp element.property
      exact ⟨⟨lift, hmem⟩, Subtype.ext hvalue⟩
    have himage : ambientComponent.map second =
        (component.map restriction).map targetNormalizer.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    have himageQuasisimple : IsQuasisimple image := by
      rw [show image = (component.map restriction).map targetNormalizer.subtype from himage]
      exact Components.quasisimple_of_equiv
        ((component.map restriction).equivMapOfInjective targetNormalizer.subtype
          targetNormalizer.subtype_injective).symm hquasisimple
    let firstRestriction := first.domRestrict ambientComponent
    let kernelInclusion : firstRestriction.ker →* first.ker :=
      (ambientComponent.subtype.comp firstRestriction.ker.subtype).codRestrict first.ker
        fun element => element.property
    let : Group.IsSolvable firstRestriction.ker :=
      Group.isSolvable_of_isSolvable_injective
        (show Function.Injective kernelInclusion from by
          intro left right heq
          have hvalues : left.val.val = right.val.val :=
            congrArg (fun element : first.ker => (element : G)) heq
          exact Subtype.ext (Subtype.ext hvalues))
    have hkernelDisjoint : firstRestriction.ker ⊓ componentRestriction.ker = ⊥ := by
      apply le_antisymm _ bot_le
      intro element hmem
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hfirstMem : element.val ∈ first.ker := hmem.1
      have hsecondMem : element.val ∈ second.ker :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hmem.2)
      exact Subgroup.mem_bot.mp (hdisjoint ▸ ⟨hfirstMem, hsecondMem⟩)
    exact kernel_central_of_quasisimple_image firstRestriction componentRestriction
      hcomponentSurjective himageQuasisimple hkernelDisjoint
  have hbadLocal : component.map restriction ≤ TwoComponents.badSubgroup targetNormalizer :=
    le_sSup ⟨himageComponent, hnotQuasisimple⟩
  have himage : ambientComponent.map second =
      (component.map restriction).map targetNormalizer.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hbadImage : ambientComponent.map second ≤ (TwoComponents.badSubgroup G).map second := by
    rw [himage]
    exact (Subgroup.map_mono hbadLocal).trans
      ((hsecondB targetTwo htargetNe (htwo.map second)).trans
        (OddKernelBadImage.lower_image second hsecondSurjective hsecondOdd))
  let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent⟩
  let : Group.IsPerfect ambientComponent := Group.IsPerfect.map normalizer.subtype
  let : (TwoComponents.badSubgroup G).Characteristic := BadComponents.characteristic G
  exact hnotContained (SolvableKernelContainment.perfect_containment second
    ambientComponent (TwoComponents.badSubgroup G) hbadImage)

end CFSG.ComponentClassification.DisjointSolvableKernels
