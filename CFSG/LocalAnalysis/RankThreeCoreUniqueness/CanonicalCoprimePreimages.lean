module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectCoprimeLifts
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

def subgroupPreimageMap
    {G Image : Type*} [Group G] [Group Image] (homomorphism : G →* Image)
    (imageGroup : Subgroup Image) : Subgroup.comap homomorphism imageGroup →* imageGroup :=
  (homomorphism.comp (Subgroup.comap homomorphism imageGroup).subtype).codRestrict imageGroup
    (fun element => element.property)

theorem subgroupPreimageMap_surjective
    {G Image : Type*} [Group G] [Group Image] (homomorphism : G →* Image)
    (hsurjective : Function.Surjective homomorphism) (imageGroup : Subgroup Image) :
    Function.Surjective (subgroupPreimageMap homomorphism imageGroup) := by
  intro element
  obtain ⟨preimage, hpreimage⟩ := hsurjective element.val
  have hmem : preimage ∈ Subgroup.comap homomorphism imageGroup := by
    change homomorphism preimage ∈ imageGroup
    rw [hpreimage]
    exact element.property
  exact ⟨⟨preimage, hmem⟩, Subtype.ext hpreimage⟩

theorem finite_canonical_perfect_preimage_image_eq
    {G Image : Type*} [Group G] [Finite G] [Group Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (imageGroup : Subgroup Image) (hperfect : Group.IsPerfect imageGroup) :
    Subgroup.map homomorphism (perfectResidualOf (Subgroup.comap homomorphism imageGroup)) =
      imageGroup := by
  let : Group.IsPerfect imageGroup := hperfect
  let preimageGroup := Subgroup.comap homomorphism imageGroup
  let restrictedMap := subgroupPreimageMap homomorphism imageGroup
  have hresidualImage := finite_perfectResidual_surjects_to_perfect_image restrictedMap
    (subgroupPreimageMap_surjective homomorphism hsurjective imageGroup)
  have hhom : homomorphism.comp preimageGroup.subtype = imageGroup.subtype.comp restrictedMap := by
    ext element
    rfl
  have htop : Subgroup.map imageGroup.subtype ⊤ = imageGroup := by
    apply le_antisymm (Subgroup.map_subtype_le _)
    intro element helement
    exact ⟨⟨element, helement⟩, Subgroup.mem_top _, rfl⟩
  unfold perfectResidualOf
  rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hresidualImage, htop]

theorem canonical_perfect_preimage_subnormal
    {G Image : Type*} [Group G] [Group Image] (homomorphism : G →* Image)
    (imageGroup : Subgroup Image) (hsubnormal : IsSubnormal imageGroup ⊤) :
    IsSubnormal (perfectResidualOf (Subgroup.comap homomorphism imageGroup)) ⊤ := by
  let preimageGroup := Subgroup.comap homomorphism imageGroup
  let : (perfectResidual preimageGroup).Characteristic := perfectResidual_characteristic
  have hpreimageSubnormal : IsSubnormal preimageGroup ⊤ := by
    simpa only [Subgroup.comap_top] using cfsg_isSubnormal_comap homomorphism hsubnormal
  exact IsSubnormal.step (Subgroup.map_subtype_le _)
    (mapped_internal_normal_subgroup_normal_subgroupOf
      preimageGroup (perfectResidual preimageGroup) inferInstance) hpreimageSubnormal

theorem finite_canonical_coprime_perfect_preimage_quotient_equiv
    {G Image : Type*} [Group G] [Finite G] [Group Image] [Finite Image]
    (prime : ℕ) (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (hkernel : prime.Coprime (Nat.card homomorphism.ker))
    (imageGroup : Subgroup Image) (hperfect : Group.IsPerfect imageGroup)
    (himageCore : primeComplementCore (G := imageGroup) prime = ⊥) :
    let perfectLift := perfectResidualOf (Subgroup.comap homomorphism imageGroup)
    Nonempty ((perfectLift ⧸ primeComplementCore prime) ≃* imageGroup) := by
  let perfectLift := perfectResidualOf (Subgroup.comap homomorphism imageGroup)
  have himage := finite_canonical_perfect_preimage_image_eq homomorphism hsurjective
    imageGroup hperfect
  let liftedMap : perfectLift →* imageGroup :=
    (homomorphism.comp perfectLift.subtype).codRestrict imageGroup (by
      intro element
      exact himage ▸ Subgroup.mem_map_of_mem homomorphism element.property)
  have hliftedSurjective : Function.Surjective liftedMap := by
    intro element
    have hmem : element.val ∈ Subgroup.map homomorphism perfectLift := himage.symm ▸ element.property
    obtain ⟨preimage, hpreimage, hequal⟩ := hmem
    exact ⟨⟨preimage, hpreimage⟩, Subtype.ext hequal⟩
  have hkernelMap : Subgroup.map perfectLift.subtype liftedMap.ker ≤ homomorphism.ker := by
    rintro element ⟨preimage, hpreimage, rfl⟩
    exact congrArg Subtype.val hpreimage
  have hliftedKernelCoprime : prime.Coprime (Nat.card liftedMap.ker) := by
    have hdivides := Subgroup.card_dvd_of_le hkernelMap
    rw [Subgroup.card_map_of_injective perfectLift.subtype_injective] at hdivides
    exact hkernel.of_dvd_right hdivides
  have hcore := coprime_kernel_trivial_image_primeComplementCore_eq_kernel prime
    liftedMap hliftedSurjective hliftedKernelCoprime himageCore
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans
    (QuotientGroup.quotientKerEquivOfSurjective liftedMap hliftedSurjective)⟩

end CFSG.RankThreeCoreUniqueness.Helpers
