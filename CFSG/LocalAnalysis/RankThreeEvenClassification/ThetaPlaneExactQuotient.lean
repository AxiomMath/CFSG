module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneProduct

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem eq_of_same_image_prime_complement_orders_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker)
    (first second : G) (hfirst : ¬prime ∣ orderOf first) (hsecond : ¬prime ∣ orderOf second)
    (heq : homomorphism first = homomorphism second) : first = second := by
  have : Fact prime.Prime := ⟨hprime⟩
  have hcommute : Commute first second :=
    commute_of_map_commute_central_pKernel prime homomorphism hcentral hkernel first second
      (orderOf second) (hprime.coprime_iff_not_dvd.mpr hsecond) (pow_orderOf_eq_one second)
      (by rw [heq])
  have hdifference : first * second⁻¹ ∈ homomorphism.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  have hnotdvd : ¬prime ∣ orderOf (first * second⁻¹) := by
    intro hdiv
    have hproductDiv := hdiv.trans hcommute.inv_right.orderOf_mul_dvd_mul_orderOf
    rw [orderOf_inv, hprime.dvd_mul] at hproductDiv
    exact hproductDiv.elim hfirst hsecond
  have hone : (⟨first * second⁻¹, hdifference⟩ : homomorphism.ker) = 1 := by
    by_contra hne
    have hdiv := hkernel.dvd_orderOf hne
    rw [← orderOf_injective homomorphism.ker.subtype Subtype.val_injective] at hdiv
    exact hnotdvd hdiv
  exact mul_inv_eq_one.mp (congrArg Subtype.val hone)

theorem thetaPlaneCommutators_map_eq_of_element_theta_images
    {G : Type u} {H : Type v} [Group G] [Group H]
    (prime : ℕ) (homomorphism : G →* H) (plane : Subgroup G)
    (hinjective : Set.InjOn homomorphism (plane : Set G))
    (hcoreImages : ∀ element ∈ plane, element ≠ 1 →
      (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))).map homomorphism =
        thetaCoreOf prime (Subgroup.centralizer ({homomorphism element} : Set H))) :
    (thetaPlaneCommutators prime plane).map homomorphism =
      thetaPlaneCommutators prime (plane.map homomorphism) := by
  simp only [thetaPlaneCommutators, Subgroup.map_iSup, Subgroup.map_commutator]
  apply le_antisymm
  · apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    have hmappedNe : homomorphism element ≠ 1 := by
      intro heq
      exact hne (hinjective hmem plane.one_mem (heq.trans (map_one homomorphism).symm))
    rw [hcoreImages element hmem hne]
    exact le_iSup_of_le (homomorphism element)
      (le_iSup_of_le (Subgroup.mem_map_of_mem homomorphism hmem) (le_iSup_of_le hmappedNe le_rfl))
  · apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp hmem
    have hpreimageNe : preimage ≠ 1 := fun heq => hne (heq ▸ map_one homomorphism)
    rw [← hcoreImages preimage hpreimage hpreimageNe]
    exact le_iSup_of_le preimage (le_iSup_of_le hpreimage (le_iSup_of_le hpreimageNe le_rfl))

theorem thetaPlaneIntersection_map_le_of_element_theta_images
    {G : Type u} {H : Type v} [Group G] [Group H]
    (prime : ℕ) (homomorphism : G →* H) (plane : Subgroup G)
    (hcoreImages : ∀ element ∈ plane, element ≠ 1 →
      (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))).map homomorphism =
        thetaCoreOf prime (Subgroup.centralizer ({homomorphism element} : Set H))) :
    (thetaPlaneIntersection prime plane).map homomorphism ≤
      thetaPlaneIntersection prime (plane.map homomorphism) := by
  apply le_iInf
  intro element
  apply le_iInf
  intro hmem
  apply le_iInf
  intro hne
  obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp hmem
  have hpreimageNe : preimage ≠ 1 := fun heq => hne (heq ▸ map_one homomorphism)
  rw [← hcoreImages preimage hpreimage hpreimageNe]
  exact Subgroup.map_mono (thetaPlaneIntersection_le prime plane preimage hpreimage hpreimageNe)

theorem thetaPlaneIntersection_map_eq_of_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (plane : Subgroup G)
    (hinjective : Set.InjOn homomorphism (plane : Set G))
    (firstElement : G) (hfirst : firstElement ∈ plane) (hfirstNe : firstElement ≠ 1) :
    (thetaPlaneIntersection prime plane).map homomorphism =
      thetaPlaneIntersection prime (plane.map homomorphism) := by
  apply le_antisymm (thetaPlaneIntersection_map_le_of_central_pKernel prime hprime homomorphism
    hsurjective hcentral hkernel plane)
  intro target htarget
  have hfirstImageNe : homomorphism firstElement ≠ 1 := by
    intro heq
    exact hfirstNe (hinjective hfirst plane.one_mem (heq.trans (map_one homomorphism).symm))
  have hfirstCore := thetaPlaneIntersection_le prime (plane.map homomorphism)
    (homomorphism firstElement) (Subgroup.mem_map_of_mem homomorphism hfirst) hfirstImageNe htarget
  rw [← thetaCoreOf_element_centralizer_map_eq_of_central_pKernel prime hprime homomorphism
    hsurjective hcentral hkernel firstElement] at hfirstCore
  obtain ⟨preimage, hpreimage, hpreimageEq⟩ := Subgroup.mem_map.mp hfirstCore
  refine ⟨preimage, ?_, hpreimageEq⟩
  change preimage ∈ thetaPlaneIntersection prime plane
  simp only [thetaPlaneIntersection, Subgroup.mem_iInf]
  intro element helement hne
  have himageNe : homomorphism element ≠ 1 := by
    intro heq
    exact hne (hinjective helement plane.one_mem (heq.trans (map_one homomorphism).symm))
  have hcore := thetaPlaneIntersection_le prime (plane.map homomorphism)
    (homomorphism element) (Subgroup.mem_map_of_mem homomorphism helement) himageNe htarget
  rw [← thetaCoreOf_element_centralizer_map_eq_of_central_pKernel prime hprime homomorphism
    hsurjective hcentral hkernel element] at hcore
  obtain ⟨other, hother, hotherEq⟩ := Subgroup.mem_map.mp hcore
  have heq : preimage = other := eq_of_same_image_prime_complement_orders_central_pKernel
    prime hprime homomorphism hcentral hkernel preimage other
    (fun hdiv => thetaCoreOf_prime_complement prime hprime _
      (hdiv.trans (Subgroup.orderOf_dvd_natCard _ hpreimage)))
    (fun hdiv => thetaCoreOf_prime_complement prime hprime _
      (hdiv.trans (Subgroup.orderOf_dvd_natCard _ hother))) (hpreimageEq.trans hotherEq.symm)
  exact heq.symm ▸ hother

theorem thetaPlaneAlpha_map_eq_of_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (plane : Subgroup G)
    (hinjective : Set.InjOn homomorphism (plane : Set G))
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1) :
    (thetaPlaneAlpha prime plane).map homomorphism =
      thetaPlaneAlpha prime (plane.map homomorphism) := by
  rw [thetaPlaneAlpha, Subgroup.map_sup,
    thetaPlaneCommutators_map_eq_of_element_theta_images prime homomorphism plane hinjective
      (fun member _ _ => thetaCoreOf_element_centralizer_map_eq_of_central_pKernel prime hprime
        homomorphism hsurjective hcentral hkernel member),
    thetaPlaneIntersection_map_eq_of_central_pKernel prime hprime homomorphism hsurjective hcentral
      hkernel plane hinjective element hmem hne]
  rfl

theorem thetaCoreOf_element_centralizer_map_eq_of_solvable_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (plane : Subgroup G) (hpgroup : IsPGroup prime plane)
    (element : G) (helement : element ∈ plane) :
    (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))).map homomorphism =
      thetaCoreOf prime (Subgroup.centralizer ({homomorphism element} : Set H)) := by
  have hcyclicPGroup : IsPGroup prime (Subgroup.zpowers element) :=
    hpgroup.of_injective (Subgroup.inclusion (Subgroup.zpowers_le_of_mem helement))
      (Subgroup.inclusion_injective (Subgroup.zpowers_le_of_mem helement))
  have hmap := thetaCoreOf_centralizer_map_eq_of_pGroup_solvable_prime_complement_kernel
    prime hprime homomorphism hsurjective hkernelSolvable hkernelComplement
      (Subgroup.zpowers element) hcyclicPGroup
  simpa only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    MonoidHom.map_closure, Set.image_singleton] using hmap

theorem kernel_centralizer_le_element_theta_of_solvable_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (homomorphism : G →* H)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker) (element : G) :
    homomorphism.ker ⊓ Subgroup.centralizer ({element} : Set G) ≤
      thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)) := by
  have : Group.IsSolvable homomorphism.ker := hkernelSolvable
  have hle : homomorphism.ker ⊓ Subgroup.centralizer ({element} : Set G) ≤
      Subgroup.centralizer ({element} : Set G) := inf_le_right
  have hnormal : ((homomorphism.ker ⊓ Subgroup.centralizer ({element} : Set G)).subgroupOf
      (Subgroup.centralizer ({element} : Set G))).Normal := by
    rw [inf_comm]
    exact normal_intersection_subgroupOf _ homomorphism.ker ⊤ le_top le_top
      inferInstance
  exact normal_solvable_primeComplement_le_thetaCoreOf prime _ _ hle hnormal
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left))
    (fun hdiv => hkernelComplement (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left)))

theorem thetaPlaneIntersection_map_eq_of_solvable_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (plane : Subgroup G) (hpgroup : IsPGroup prime plane)
    (hinjective : Set.InjOn homomorphism (plane : Set G)) :
    (thetaPlaneIntersection prime plane).map homomorphism =
      thetaPlaneIntersection prime (plane.map homomorphism) := by
  have hcoreImages : ∀ element ∈ plane, element ≠ 1 →
      (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))).map homomorphism =
        thetaCoreOf prime (Subgroup.centralizer ({homomorphism element} : Set H)) :=
    fun element helement _ =>
      thetaCoreOf_element_centralizer_map_eq_of_solvable_prime_complement_kernel prime hprime
        homomorphism hsurjective hkernelSolvable hkernelComplement plane hpgroup element helement
  apply le_antisymm (thetaPlaneIntersection_map_le_of_element_theta_images prime homomorphism plane
    hcoreImages)
  intro target htarget
  obtain ⟨preimage, hcentralizer, hpreimageEq⟩ :=
    exists_centralizer_preimage_of_pGroup_prime_complement_kernel prime hprime homomorphism
      hsurjective hkernelComplement plane hpgroup target
        (thetaPlaneIntersection_le_centralizer prime (plane.map homomorphism) htarget)
  refine ⟨preimage, ?_, hpreimageEq⟩
  change preimage ∈ thetaPlaneIntersection prime plane
  simp only [thetaPlaneIntersection, Subgroup.mem_iInf]
  intro element helement hne
  have himageNe : homomorphism element ≠ 1 := by
    intro heq
    exact hne (hinjective helement plane.one_mem (heq.trans (map_one homomorphism).symm))
  have hcore := thetaPlaneIntersection_le prime (plane.map homomorphism)
    (homomorphism element) (Subgroup.mem_map_of_mem homomorphism helement) himageNe htarget
  rw [← hcoreImages element helement hne] at hcore
  obtain ⟨other, hother, hotherEq⟩ := Subgroup.mem_map.mp hcore
  have hdifferenceKernel : other⁻¹ * preimage ∈ homomorphism.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hotherEq, hpreimageEq, inv_mul_cancel]
  have hpreimageCommutes : preimage ∈ Subgroup.centralizer ({element} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr helement) hcentralizer
  have hdifferenceCentralizer : other⁻¹ * preimage ∈ Subgroup.centralizer ({element} : Set G) :=
    (Subgroup.centralizer ({element} : Set G)).mul_mem
      ((Subgroup.centralizer ({element} : Set G)).inv_mem (thetaCoreOf_le prime _ hother))
      hpreimageCommutes
  have hdifferenceTheta := kernel_centralizer_le_element_theta_of_solvable_prime_complement_kernel
    prime homomorphism hkernelSolvable hkernelComplement element
      ⟨hdifferenceKernel, hdifferenceCentralizer⟩
  simpa only [mul_inv_cancel_left] using
    (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))).mul_mem hother hdifferenceTheta

theorem thetaPlaneAlpha_map_eq_of_solvable_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (plane : Subgroup G) (hpgroup : IsPGroup prime plane)
    (hinjective : Set.InjOn homomorphism (plane : Set G)) :
    (thetaPlaneAlpha prime plane).map homomorphism =
      thetaPlaneAlpha prime (plane.map homomorphism) := by
  rw [thetaPlaneAlpha, Subgroup.map_sup,
    thetaPlaneCommutators_map_eq_of_element_theta_images prime homomorphism plane hinjective
      (fun element helement _ =>
        thetaCoreOf_element_centralizer_map_eq_of_solvable_prime_complement_kernel prime hprime
          homomorphism hsurjective hkernelSolvable hkernelComplement plane hpgroup element helement),
    thetaPlaneIntersection_map_eq_of_solvable_prime_complement_kernel prime hprime homomorphism
      hsurjective hkernelSolvable hkernelComplement plane hpgroup hinjective]
  rfl

theorem injOn_subgroup_of_disjoint_kernel {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (subgroup : Subgroup G) (hdisjoint : Disjoint subgroup homomorphism.ker) :
    Set.InjOn homomorphism (subgroup : Set G) := by
  intro first hfirst second hsecond heq
  apply mul_inv_eq_one.mp
  apply Subgroup.disjoint_def.mp hdisjoint (subgroup.mul_mem hfirst (subgroup.inv_mem hsecond))
  apply MonoidHom.mem_ker.mpr
  rw [map_mul, map_inv, heq, mul_inv_cancel]

theorem injOn_pSubgroup_of_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (subgroup : Subgroup G) (hpgroup : IsPGroup prime subgroup) :
    Set.InjOn homomorphism (subgroup : Set G) := by
  exact injOn_subgroup_of_disjoint_kernel homomorphism subgroup
    (prime_complement_disjoint_pSubgroup prime hprime homomorphism.ker subgroup
      hkernelComplement hpgroup).symm

theorem card_subgroup_map_eq_of_injOn {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (subgroup : Subgroup G)
    (hinjective : Set.InjOn homomorphism (subgroup : Set G)) :
    Nat.card (subgroup.map homomorphism) = Nat.card subgroup := by
  have hrestrictionInjective : Function.Injective (homomorphism.subgroupMap subgroup) := by
    intro first second heq
    apply Subtype.ext
    exact hinjective first.property second.property (congrArg Subtype.val heq)
  exact (Nat.card_congr (Equiv.ofBijective (homomorphism.subgroupMap subgroup)
    ⟨hrestrictionInjective, homomorphism.subgroupMap_surjective subgroup⟩)).symm

theorem thetaPlaneAlpha_le_theta_iff_of_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (plane : Subgroup G)
    (hcomm : IsMulCommutative plane) (hinjective : Set.InjOn homomorphism (plane : Set G))
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1) :
    thetaPlaneAlpha prime plane ≤ solvablePrimeComplementCore G prime ↔
      thetaPlaneAlpha prime (plane.map homomorphism) ≤ solvablePrimeComplementCore H prime := by
  constructor
  · intro hle
    rw [← thetaPlaneAlpha_map_eq_of_central_pKernel prime hprime homomorphism hsurjective
      hcentral hkernel plane hinjective element hmem hne]
    exact (Subgroup.map_mono hle).trans (le_of_eq
      (solvablePrimeComplementCore_map_eq_of_central_kernel prime hprime homomorphism
        hsurjective hcentral))
  · exact thetaPlaneAlpha_le_of_quotient_alpha_le_of_injective_plane prime hprime homomorphism
      hsurjective hcentral hkernel plane hcomm hinjective element hmem hne

theorem thetaPlaneAlpha_le_theta_iff_of_solvable_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (plane : Subgroup G) (hpgroup : IsPGroup prime plane) :
    thetaPlaneAlpha prime plane ≤ solvablePrimeComplementCore G prime ↔
      thetaPlaneAlpha prime (plane.map homomorphism) ≤ solvablePrimeComplementCore H prime := by
  have hinjective := injOn_pSubgroup_of_prime_complement_kernel prime hprime homomorphism
    hkernelComplement plane hpgroup
  have hmap := thetaPlaneAlpha_map_eq_of_solvable_prime_complement_kernel prime hprime homomorphism
    hsurjective hkernelSolvable hkernelComplement plane hpgroup hinjective
  have hcoreMap := solvablePrimeComplementCore_map_eq_of_solvable_prime_complement_kernel prime hprime
    homomorphism hsurjective hkernelSolvable hkernelComplement
  constructor
  · intro hle
    rw [← hmap, ← hcoreMap]
    exact Subgroup.map_mono hle
  · intro hle
    have hcomap := Subgroup.map_le_iff_le_comap.mp (hmap.le.trans hle)
    rw [solvablePrimeComplementCore_comap_eq_of_solvable_prime_complement_kernel prime hprime
      homomorphism hsurjective hkernelSolvable hkernelComplement] at hcomap
    exact hcomap

end CFSG.RankThreeEvenClassification.Helpers
