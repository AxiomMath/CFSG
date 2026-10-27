module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaIntersection

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem solvablePrimeComplementCore_map_le_of_surjective {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (homomorphism : G →* otherGroup) (hsurjective : Function.Surjective homomorphism) :
    (solvablePrimeComplementCore G prime).map homomorphism ≤
      solvablePrimeComplementCore otherGroup prime := by
  obtain ⟨hnormal, hsolvable, hcomplement⟩ := solvablePrimeComplementCore_properties G prime hprime
  have : Group.IsSolvable (solvablePrimeComplementCore G prime) := hsolvable
  apply le_solvablePrimeComplementCore prime
  · exact hnormal.map homomorphism hsurjective
  · exact Group.isSolvable_of_surjective
      (f := homomorphism.subgroupMap (solvablePrimeComplementCore G prime))
      (homomorphism.subgroupMap_surjective _)
  · exact fun hdiv => hcomplement (hdiv.trans (Subgroup.card_map_dvd _ homomorphism))

theorem complement_normal_of_central_kernel {G : Type u} [Group G]
    (kernel complement : Subgroup G) (hcentral : kernel ≤ Subgroup.center G)
    (hcomplement : complement.IsComplement' kernel) : complement.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  rw [← hcomplement.sup_eq_top]
  exact sup_le Subgroup.le_normalizer
    (hcentral.trans (Subgroup.center_le_normalizer (complement : Set G)))

theorem solvable_of_solvable_kernel_and_range {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (homomorphism : G →* otherGroup)
    (hsurjective : Function.Surjective homomorphism)
    (hkernel : Group.IsSolvable homomorphism.ker) (hrange : Group.IsSolvable otherGroup) :
    Group.IsSolvable G := by
  have : Group.IsSolvable otherGroup := hrange
  apply (Group.isSolvable_iff_subgroup_quotient homomorphism.ker).mpr
  refine ⟨hkernel, ?_⟩
  let equivalence := QuotientGroup.quotientKerEquivOfSurjective homomorphism hsurjective
  exact Group.isSolvable_of_surjective (f := equivalence.symm.toMonoidHom)
    equivalence.symm.surjective

theorem solvablePrimeComplementCore_covers_central_pKernel_quotient {G : Type u}
    {otherGroup : Type v} [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* otherGroup)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (hsolvable : Group.IsSolvable otherGroup)
    (hcomplement : ¬prime ∣ Nat.card otherGroup) :
    (solvablePrimeComplementCore G prime).map homomorphism = ⊤ := by
  have : Fact prime.Prime := ⟨hprime⟩
  have hkernelSolvable : Group.IsSolvable homomorphism.ker := by
    have : Group.IsNilpotent homomorphism.ker := hkernel.isNilpotent
    infer_instance
  have hgroupSolvable := solvable_of_solvable_kernel_and_range homomorphism hsurjective
    hkernelSolvable hsolvable
  obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp hkernel
  let equivalence := QuotientGroup.quotientKerEquivOfSurjective homomorphism hsurjective
  have hindex : homomorphism.ker.index = Nat.card otherGroup :=
    (Subgroup.index_eq_card homomorphism.ker).trans (Nat.card_congr equivalence.toEquiv)
  have hcoprime : (Nat.card homomorphism.ker).Coprime homomorphism.ker.index := by
    rw [hcard, hindex]
    exact (hprime.coprime_pow_of_not_dvd hcomplement).symm
  obtain ⟨complement, hcomplementKernel⟩ := Subgroup.exists_left_complement'_of_coprime hcoprime
  have hnormal := complement_normal_of_central_kernel homomorphism.ker complement hcentral
    hcomplementKernel
  have hcomplementCard : Nat.card complement = Nat.card otherGroup :=
    hcomplementKernel.index_eq_card.symm.trans hindex
  have : Group.IsSolvable G := hgroupSolvable
  have hcore := le_solvablePrimeComplementCore prime complement hnormal inferInstance
    (hcomplementCard.symm ▸ hcomplement)
  have hmapped : complement.map homomorphism = ⊤ := by
    have heq := congrArg (Subgroup.map homomorphism) hcomplementKernel.sup_eq_top
    simpa only [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq,
      Subgroup.map_top_of_surjective homomorphism hsurjective] using heq
  apply top_le_iff.mp
  rw [← hmapped]
  exact Subgroup.map_mono hcore

theorem solvablePrimeComplementCore_covers_central_kernel_quotient {G : Type u}
    {otherGroup : Type v} [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* otherGroup)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G) (hsolvable : Group.IsSolvable otherGroup)
    (hcomplement : ¬prime ∣ Nat.card otherGroup) :
    (solvablePrimeComplementCore G prime).map homomorphism = ⊤ := by
  classical
  have : Fact prime.Prime := ⟨hprime⟩
  let sylow : Sylow prime G := Classical.choice inferInstance
  have hmappedPGroup := sylow.isPGroup'.map homomorphism
  have hmappedCard : Nat.card ((sylow : Subgroup G).map homomorphism) = 1 := by
    rcases hmappedPGroup.card_eq_or_dvd with hone | hdiv
    · exact hone
    · exact False.elim (hcomplement (hdiv.trans (Subgroup.card_subgroup_dvd_card _)))
  have hsylowKernel : (sylow : Subgroup G) ≤ homomorphism.ker :=
    (Subgroup.map_eq_bot_iff (sylow : Subgroup G)).mp (Subgroup.card_eq_one.mp hmappedCard)
  have hsylowCentral := hsylowKernel.trans hcentral
  have hsylowNormal : (sylow : Subgroup G).Normal := by
    refine ⟨?_⟩
    intro element helement conjugator
    have hcommute := Subgroup.mem_center_iff.mp (hsylowCentral helement) conjugator
    rw [hcommute, mul_assoc, mul_inv_cancel, mul_one]
    exact helement
  have : (sylow : Subgroup G).Normal := hsylowNormal
  obtain ⟨complement, hcomplementSylow⟩ := Subgroup.exists_left_complement'_of_coprime
    sylow.card_coprime_index
  have hnormal := complement_normal_of_central_kernel (sylow : Subgroup G) complement
    hsylowCentral hcomplementSylow
  have hcomplementPrime : ¬prime ∣ Nat.card complement := by
    rw [← hcomplementSylow.index_eq_card]
    exact sylow.not_dvd_index
  have hkernelCommutative : IsMulCommutative homomorphism.ker := by
    apply isMulCommutative_iff.mpr
    intro first second
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral second.property) first
  have hkernelSolvable : Group.IsSolvable homomorphism.ker :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp hkernelCommutative)
  have : Group.IsSolvable G := solvable_of_solvable_kernel_and_range homomorphism
    hsurjective hkernelSolvable hsolvable
  have hcore := le_solvablePrimeComplementCore prime complement hnormal inferInstance hcomplementPrime
  have hmapped : complement.map homomorphism = ⊤ := by
    have hsylowMap : (sylow : Subgroup G).map homomorphism = ⊥ := Subgroup.card_eq_one.mp hmappedCard
    have heq := congrArg (Subgroup.map homomorphism) hcomplementSylow.sup_eq_top
    simpa only [Subgroup.map_sup, hsylowMap, sup_bot_eq,
      Subgroup.map_top_of_surjective homomorphism hsurjective] using heq
  apply top_le_iff.mp
  rw [← hmapped]
  exact Subgroup.map_mono hcore

theorem solvablePrimeComplementCore_map_eq_of_central_kernel {G : Type u}
    {otherGroup : Type v} [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* otherGroup)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G) :
    (solvablePrimeComplementCore G prime).map homomorphism =
      solvablePrimeComplementCore otherGroup prime := by
  apply le_antisymm (solvablePrimeComplementCore_map_le_of_surjective prime hprime
    homomorphism hsurjective)
  let targetCore := solvablePrimeComplementCore otherGroup prime
  let preimage := targetCore.comap homomorphism
  let restriction : preimage →* targetCore :=
    { toFun := fun element => ⟨homomorphism element, element.property⟩
      map_one' := Subtype.ext (map_one homomorphism)
      map_mul' := fun first second => Subtype.ext
        (map_mul homomorphism (first : G) (second : G)) }
  have hrestrictionSurjective : Function.Surjective restriction := by
    intro element
    obtain ⟨preimageElement, heq⟩ := hsurjective element
    refine ⟨⟨preimageElement, ?_⟩, ?_⟩
    · change homomorphism preimageElement ∈ targetCore
      exact heq.symm ▸ element.property
    · exact Subtype.ext heq
  have hrestrictionCentral : restriction.ker ≤ Subgroup.center preimage := by
    intro element helement
    have hcentralElement := hcentral
      (show (element : G) ∈ homomorphism.ker from
        (congrArg Subtype.val (MonoidHom.mem_ker.mp helement)))
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hcentralElement other
  obtain ⟨htargetNormal, htargetSolvable, htargetComplement⟩ :=
    solvablePrimeComplementCore_properties otherGroup prime hprime
  have hcover := solvablePrimeComplementCore_covers_central_kernel_quotient prime hprime
    restriction hrestrictionSurjective hrestrictionCentral
    htargetSolvable htargetComplement
  have hpreimageNormal : preimage.Normal := htargetNormal.comap homomorphism
  have hcoreNormal := thetaCoreOf_normal_of_normal prime hprime preimage hpreimageNormal
  have hcoreLe := le_solvablePrimeComplementCore prime (thetaCoreOf prime preimage) hcoreNormal
    (thetaCoreOf_solvable prime hprime preimage) (thetaCoreOf_prime_complement prime hprime preimage)
  have hcomposition : targetCore.subtype.comp restriction = homomorphism.comp preimage.subtype := by
    ext element
    rfl
  have hmapped : (thetaCoreOf prime preimage).map homomorphism = targetCore := by
    have hmap := congrArg (Subgroup.map targetCore.subtype) hcover
    rw [Subgroup.map_map, hcomposition, ← Subgroup.map_map] at hmap
    simpa only [thetaCoreOf, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hmap
  change targetCore ≤ (solvablePrimeComplementCore G prime).map homomorphism
  rw [← hmapped]
  exact Subgroup.map_mono hcoreLe

end CFSG.RankThreeEvenClassification.Helpers
