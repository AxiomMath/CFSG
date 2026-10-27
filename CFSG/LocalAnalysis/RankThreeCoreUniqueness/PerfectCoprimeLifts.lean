module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralComponentLifts

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem finite_surjective_perfect_image_has_characteristic_perfect_lift
    {G Image : Type*} [Group G] [Finite G] [Group Image] [Group.IsPerfect Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism) :
    ∃ perfectGroup : Subgroup G, perfectGroup.Characteristic ∧ Group.IsPerfect perfectGroup ∧
      Subgroup.map homomorphism perfectGroup = ⊤ := by
  classical
  obtain ⟨perfectGroup, hminimal⟩ := (Set.toFinite (Set.range (derivedSeries G))).exists_minimal
    ⟨derivedSeries G 0, ⟨0, rfl⟩⟩
  obtain ⟨index, rfl⟩ := hminimal.prop
  have hnext : derivedSeries G (index + 1) = derivedSeries G index :=
    hminimal.eq_of_le ⟨index + 1, rfl⟩ (derivedSeries_antitone G (Nat.le_succ index))
  have hperfect : Group.IsPerfect (derivedSeries G index) := by
    apply Subgroup.isPerfect_iff.mpr
    rwa [derivedSeries_succ] at hnext
  have himage := derivedSeries_le_map_derivedSeries hsurjective index
  rw [Group.IsPerfect.derivedSeries_eq_top] at himage
  exact ⟨derivedSeries G index, inferInstance, hperfect, top_le_iff.mp himage⟩

theorem coprime_kernel_trivial_image_primeComplementCore_eq_kernel
    {G Image : Type*} [Group G] [Finite G] [Group Image] [Finite Image]
    (prime : ℕ) (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (hkernel : prime.Coprime (Nat.card homomorphism.ker))
    (himageCore : primeComplementCore (G := Image) prime = ⊥) :
    primeComplementCore (G := G) prime = homomorphism.ker := by
  apply le_antisymm
  · have himage := normal_coprime_le_primeComplementCore prime
      (Subgroup.map homomorphism (primeComplementCore prime))
      ((primeComplementCore_normal prime).map homomorphism hsurjective)
      ((primeComplementCore_coprime prime).of_dvd_right
        ((primeComplementCore prime).card_map_dvd homomorphism))
    rw [himageCore] at himage
    intro element helement
    exact Subgroup.mem_bot.mp (himage ⟨element, helement, rfl⟩)
  · exact normal_coprime_le_primeComplementCore prime homomorphism.ker inferInstance hkernel

theorem normal_subgroupOf_comap
    {G Image : Type*} [Group G] [Group Image] (homomorphism : G →* Image)
    (subgroup overgroup : Subgroup Image) (hbound : subgroup ≤ overgroup)
    (hnormal : (subgroup.subgroupOf overgroup).Normal) :
    ((Subgroup.comap homomorphism subgroup).subgroupOf
      (Subgroup.comap homomorphism overgroup)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (Subgroup.comap_mono hbound)).mpr
  intro element conjugator helement hconjugator
  change homomorphism (conjugator * element * conjugator⁻¹) ∈ subgroup
  rw [map_mul, map_mul, map_inv]
  exact (Subgroup.normal_subgroupOf_iff hbound).mp hnormal
    (homomorphism element) (homomorphism conjugator) helement hconjugator

theorem cfsg_isSubnormal_comap
    {G Image : Type*} [Group G] [Group Image] (homomorphism : G →* Image)
    {subgroup overgroup : Subgroup Image} (hsubnormal : IsSubnormal subgroup overgroup) :
    IsSubnormal (Subgroup.comap homomorphism subgroup) (Subgroup.comap homomorphism overgroup) :=
  hsubnormal.comap homomorphism

theorem coprime_extension_perfect_subnormal_has_perfect_lift
    {G Image : Type*} [Group G] [Finite G] [Group Image] [Finite Image]
    (prime : ℕ) (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (hkernel : prime.Coprime (Nat.card homomorphism.ker))
    (perfectImage : Subgroup Image) (hperfect : Group.IsPerfect perfectImage)
    (hsubnormal : IsSubnormal perfectImage ⊤)
    (himageCore : primeComplementCore (G := perfectImage) prime = ⊥) :
    ∃ perfectLift : Subgroup G, Group.IsPerfect perfectLift ∧ IsSubnormal perfectLift ⊤ ∧
      Subgroup.map homomorphism perfectLift = perfectImage ∧
      ∃ liftedMap : perfectLift →* perfectImage, Function.Surjective liftedMap ∧
        primeComplementCore (G := perfectLift) prime = liftedMap.ker ∧
        Nonempty ((perfectLift ⧸ primeComplementCore prime) ≃* perfectImage) := by
  let : Group.IsPerfect perfectImage := hperfect
  let preimageGroup := Subgroup.comap homomorphism perfectImage
  let restrictedMap : preimageGroup →* perfectImage :=
    (homomorphism.comp preimageGroup.subtype).codRestrict perfectImage
      (fun element => element.property)
  have hrestrictedSurjective : Function.Surjective restrictedMap := by
    intro element
    obtain ⟨preimage, hpreimage⟩ := hsurjective element.val
    have hmem : preimage ∈ preimageGroup := by
      change homomorphism preimage ∈ perfectImage
      rw [hpreimage]
      exact element.property
    exact ⟨⟨preimage, hmem⟩, Subtype.ext hpreimage⟩
  obtain ⟨residualGroup, hcharacteristic, hresidualPerfect, hresidualImage⟩ :=
    finite_surjective_perfect_image_has_characteristic_perfect_lift
      restrictedMap hrestrictedSurjective
  let : residualGroup.Characteristic := hcharacteristic
  let perfectLift := Subgroup.map preimageGroup.subtype residualGroup
  let liftEquiv := residualGroup.equivMapOfInjective preimageGroup.subtype
    preimageGroup.subtype_injective
  let residualMap := restrictedMap.comp residualGroup.subtype
  have hresidualSurjective : Function.Surjective residualMap := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hresidualImage
  let liftedMap := residualMap.comp liftEquiv.symm.toMonoidHom
  have hliftedSurjective : Function.Surjective liftedMap :=
    hresidualSurjective.comp liftEquiv.symm.surjective
  have hliftedPerfect : Group.IsPerfect perfectLift := by
    apply Subgroup.isPerfect_iff.mpr
    dsimp only [perfectLift]
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hresidualPerfect]
  have hpreimageSubnormal : IsSubnormal preimageGroup ⊤ := by
    simpa only [Subgroup.comap_top] using cfsg_isSubnormal_comap homomorphism hsubnormal
  have hliftedSubnormal : IsSubnormal perfectLift ⊤ :=
    IsSubnormal.step (Subgroup.map_subtype_le _)
      (mapped_internal_normal_subgroup_normal_subgroupOf preimageGroup residualGroup inferInstance)
      hpreimageSubnormal
  have hcompatibility : perfectImage.subtype.comp liftedMap =
      homomorphism.comp perfectLift.subtype := by
    ext element
    change homomorphism (preimageGroup.subtype
      (residualGroup.subtype (liftEquiv.symm element))) = homomorphism element.val
    exact congrArg homomorphism (congrArg Subtype.val (liftEquiv.apply_symm_apply element))
  have hkernelMap : Subgroup.map perfectLift.subtype liftedMap.ker ≤ homomorphism.ker := by
    rintro element ⟨preimage, hpreimage, rfl⟩
    have hcompat := DFunLike.congr_fun hcompatibility preimage
    change perfectImage.subtype (liftedMap preimage) = homomorphism preimage.val at hcompat
    rw [hpreimage, map_one] at hcompat
    exact hcompat.symm
  have hliftedKernelCoprime : prime.Coprime (Nat.card liftedMap.ker) := by
    have hdivides := Subgroup.card_dvd_of_le hkernelMap
    rw [Subgroup.card_map_of_injective perfectLift.subtype_injective] at hdivides
    exact hkernel.of_dvd_right hdivides
  have hliftedCore := coprime_kernel_trivial_image_primeComplementCore_eq_kernel prime
    liftedMap hliftedSurjective hliftedKernelCoprime himageCore
  have himage : Subgroup.map homomorphism perfectLift = perfectImage := by
    apply le_antisymm
    · rintro element ⟨preimage, hpreimage, rfl⟩
      have hcompat := DFunLike.congr_fun hcompatibility ⟨preimage, hpreimage⟩
      exact hcompat ▸ (liftedMap ⟨preimage, hpreimage⟩).property
    · intro element helement
      obtain ⟨preimage, hpreimage⟩ := hliftedSurjective ⟨element, helement⟩
      refine ⟨preimage.val, preimage.property, ?_⟩
      have hcompat := DFunLike.congr_fun hcompatibility preimage
      change (liftedMap preimage).val = homomorphism preimage.val at hcompat
      rw [← hcompat, hpreimage]
  exact ⟨perfectLift, hliftedPerfect, hliftedSubnormal, himage,
    liftedMap, hliftedSurjective, hliftedCore,
    ⟨(QuotientGroup.quotientMulEquivOfEq hliftedCore).trans
      (QuotientGroup.quotientKerEquivOfSurjective liftedMap hliftedSurjective)⟩⟩

end CFSG.RankThreeCoreUniqueness.Helpers
