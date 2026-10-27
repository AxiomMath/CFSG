module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneQuotient

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem card_eq_card_target_mul_card_kernel_of_surjective
    {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (hsurjective : Function.Surjective homomorphism) :
    Nat.card G = Nat.card H * Nat.card homomorphism.ker := by
  have hcard := homomorphism.ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective homomorphism hsurjective).toEquiv]
    at hcard
  exact hcard

theorem prime_complement_of_prime_complement_kernel_target
    {G : Type u} {H : Type v} [Group G] [Group H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernel : ¬prime ∣ Nat.card homomorphism.ker) (htarget : ¬prime ∣ Nat.card H) :
    ¬prime ∣ Nat.card G := by
  rw [card_eq_card_target_mul_card_kernel_of_surjective homomorphism hsurjective]
  exact fun hdiv => (hprime.dvd_mul.mp hdiv).elim htarget hkernel

theorem solvablePrimeComplementCore_covers_solvable_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (htargetSolvable : Group.IsSolvable H) (htargetComplement : ¬prime ∣ Nat.card H) :
    solvablePrimeComplementCore G prime = ⊤ := by
  apply top_le_iff.mp
  apply le_solvablePrimeComplementCore prime ⊤ inferInstance
  · have : Group.IsSolvable G := solvable_of_solvable_kernel_and_range homomorphism hsurjective
      hkernelSolvable htargetSolvable
    infer_instance
  · simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using
      prime_complement_of_prime_complement_kernel_target prime hprime homomorphism
        hsurjective hkernelComplement htargetComplement

theorem solvablePrimeComplementCore_comap_eq_of_solvable_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker) :
    (solvablePrimeComplementCore H prime).comap homomorphism =
      solvablePrimeComplementCore G prime := by
  let targetCore := solvablePrimeComplementCore H prime
  let preimage := targetCore.comap homomorphism
  let restriction : preimage →* targetCore :=
    { toFun := fun element => ⟨homomorphism element, element.property⟩
      map_one' := Subtype.ext (map_one homomorphism)
      map_mul' := fun first second => Subtype.ext
        (map_mul homomorphism (first : G) (second : G)) }
  have hrestrictionSurjective : Function.Surjective restriction := by
    intro element
    obtain ⟨preimageElement, heq⟩ := hsurjective element
    refine ⟨⟨preimageElement, ?_⟩, Subtype.ext heq⟩
    change homomorphism preimageElement ∈ targetCore
    exact heq.symm ▸ element.property
  let kernelMap : restriction.ker →* homomorphism.ker :=
    { toFun := fun element =>
        ⟨((element : preimage) : G), congrArg Subtype.val (MonoidHom.mem_ker.mp element.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hkernelMapInjective : Function.Injective kernelMap := by
    intro first second heq
    exact Subtype.ext (Subtype.ext
      (congrArg (fun element : homomorphism.ker => (element : G)) heq))
  have hrestrictionKernelSolvable : Group.IsSolvable restriction.ker := by
    have : Group.IsSolvable homomorphism.ker := hkernelSolvable
    exact Group.isSolvable_of_isSolvable_injective (f := kernelMap) hkernelMapInjective
  have hrestrictionKernelComplement : ¬prime ∣ Nat.card restriction.ker := by
    exact fun hdiv => hkernelComplement (hdiv.trans
      (Subgroup.card_dvd_of_injective kernelMap hkernelMapInjective))
  have hpreimageCore := solvablePrimeComplementCore_covers_solvable_prime_complement_kernel
    prime hprime restriction hrestrictionSurjective hrestrictionKernelSolvable
    hrestrictionKernelComplement (solvablePrimeComplementCore_properties H prime hprime).2.1
    (solvablePrimeComplementCore_properties H prime hprime).2.2
  apply le_antisymm
  · have hnormal : preimage.Normal :=
      (solvablePrimeComplementCore_properties H prime hprime).1.comap homomorphism
    have hthetaLe := normal_solvable_primeComplement_le_thetaCoreOf prime
      (thetaCoreOf prime preimage) ⊤ le_top
      ((thetaCoreOf_normal_of_normal prime hprime preimage hnormal).subgroupOf ⊤)
      (thetaCoreOf_solvable prime hprime preimage) (thetaCoreOf_prime_complement prime hprime preimage)
    have hthetaEq : thetaCoreOf prime preimage = preimage := by
      rw [thetaCoreOf, hpreimageCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hthetaEq, thetaCoreOf_top prime hprime] at hthetaLe
    exact hthetaLe
  · exact Subgroup.map_le_iff_le_comap.mp
      (solvablePrimeComplementCore_map_le_of_surjective prime hprime homomorphism hsurjective)

theorem solvablePrimeComplementCore_map_eq_of_solvable_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker) :
    (solvablePrimeComplementCore G prime).map homomorphism =
      solvablePrimeComplementCore H prime := by
  rw [← solvablePrimeComplementCore_comap_eq_of_solvable_prime_complement_kernel prime hprime
    homomorphism hsurjective hkernelSolvable hkernelComplement,
    Subgroup.map_comap_eq_self_of_surjective hsurjective]

theorem solvablePrimeComplementCore_quotient_eq_bot {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime)
    (hnormal : (solvablePrimeComplementCore G prime).Normal) :
    solvablePrimeComplementCore (G ⧸ solvablePrimeComplementCore G prime) prime = ⊥ := by
  have : (solvablePrimeComplementCore G prime).Normal := hnormal
  let quotient := QuotientGroup.mk' (solvablePrimeComplementCore G prime)
  have hkernel : quotient.ker = solvablePrimeComplementCore G prime := QuotientGroup.ker_mk' _
  have hsolvable : Group.IsSolvable quotient.ker := by
    rw [hkernel]
    exact (solvablePrimeComplementCore_properties G prime hprime).2.1
  have hcomplement : ¬prime ∣ Nat.card quotient.ker := by
    rw [hkernel]
    exact (solvablePrimeComplementCore_properties G prime hprime).2.2
  rw [← solvablePrimeComplementCore_map_eq_of_solvable_prime_complement_kernel prime hprime
    quotient (QuotientGroup.mk'_surjective _) hsolvable hcomplement]
  exact (Subgroup.map_eq_bot_iff _).mpr hkernel.ge

end CFSG.RankThreeEvenClassification.Helpers
