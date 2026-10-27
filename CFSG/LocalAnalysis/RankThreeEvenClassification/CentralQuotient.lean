module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaQuotient

public section

open scoped commutatorElement

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem commute_of_map_commute_central_pKernel {G : Type u} {H : Type v}
    [Group G] [Group H] (prime : ℕ) (homomorphism : G →* H)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (element actor : G)
    (exponent : ℕ) (hcoprime : prime.Coprime exponent) (hpower : actor ^ exponent = 1)
    (hcommute : Commute (homomorphism element) (homomorphism actor)) :
    Commute element actor := by
  have hcommutator : ⁅element, actor⁆ ∈ homomorphism.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr hcommute
  have hcommutatorCentral := hcentral hcommutator
  have hproductCommute : Commute ⁅element, actor⁆ actor := by
    exact (Subgroup.mem_center_iff.mp hcommutatorCentral actor).symm
  have hconjugate : (MulAut.conj element) actor = ⁅element, actor⁆ * actor := by
    simp only [MulAut.conj_apply, commutatorElement_def]
    group
  have hcommutatorPower : ⁅element, actor⁆ ^ exponent = 1 := by
    have hconjugatePower := congrArg (MulAut.conj element) hpower
    rw [map_pow, hconjugate, hproductCommute.mul_pow, hpower, mul_one, map_one]
      at hconjugatePower
    exact hconjugatePower
  have hsubtypePower : (⟨⁅element, actor⁆, hcommutator⟩ : homomorphism.ker) ^ exponent = 1 := by
    exact Subtype.ext hcommutatorPower
  have hsubtypeOne : (⟨⁅element, actor⁆, hcommutator⟩ : homomorphism.ker) = 1 := by
    apply (hkernel.powEquiv hcoprime).injective
    simpa only [IsPGroup.powEquiv_apply, one_pow] using hsubtypePower
  apply commutatorElement_eq_one_iff_commute.mp
  exact congrArg Subtype.val hsubtypeOne

theorem commute_of_map_commute_central_pKernel_prime_complement
    {G : Type u} {H : Type v} [Group G] [Group H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (subgroup : Subgroup G)
    (hcomplement : ¬prime ∣ Nat.card subgroup) (element actor : G) (hactor : actor ∈ subgroup)
    (hcommute : Commute (homomorphism element) (homomorphism actor)) :
    Commute element actor := by
  apply commute_of_map_commute_central_pKernel prime homomorphism hcentral hkernel
    element actor (orderOf actor) _ (pow_orderOf_eq_one actor) hcommute
  exact hprime.coprime_iff_not_dvd.mpr fun hdiv =>
    hcomplement (hdiv.trans (subgroup.orderOf_dvd_natCard hactor))

theorem centralizer_le_comap_centralizer_map {G : Type u} {H : Type v}
    [Group G] [Group H] (homomorphism : G →* H) (subgroup : Subgroup G) :
    Subgroup.centralizer (subgroup : Set G) ≤
      (Subgroup.centralizer (subgroup.map homomorphism : Set H)).comap homomorphism := by
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro actor hactor
  obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp hactor
  simpa only [map_mul] using
    congrArg homomorphism (Subgroup.mem_centralizer_iff.mp helement preimage hpreimage)

theorem kernel_le_comap_centralizer_map {G : Type u} {H : Type v}
    [Group G] [Group H] (homomorphism : G →* H) (subgroup : Subgroup G) :
    homomorphism.ker ≤
      (Subgroup.centralizer (subgroup.map homomorphism : Set H)).comap homomorphism := by
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro actor _
  rw [MonoidHom.mem_ker.mp helement, mul_one, one_mul]

theorem normalizes_comap_centralizer_map {G : Type u} {H : Type v}
    [Group G] [Group H] (homomorphism : G →* H) (subgroup : Subgroup G) :
    subgroup ≤ Subgroup.normalizer
      (((Subgroup.centralizer (subgroup.map homomorphism : Set H)).comap homomorphism) : Set G) := by
  apply Subgroup.le_normalizer_iff_commutator_le_right.mpr
  apply Subgroup.commutator_le.mpr
  intro actor hactor element helement
  apply kernel_le_comap_centralizer_map homomorphism subgroup
  apply MonoidHom.mem_ker.mpr
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  exact Subgroup.mem_centralizer_iff.mp helement (homomorphism actor)
    (Subgroup.mem_map_of_mem homomorphism hactor)

theorem centralizer_normal_in_comap_centralizer_map {G : Type u} {H : Type v}
    [Group G] [Group H] (homomorphism : G →* H)
    (hcentral : homomorphism.ker ≤ Subgroup.center G) (subgroup : Subgroup G) :
    ((Subgroup.centralizer (subgroup : Set G)).subgroupOf
      ((Subgroup.centralizer (subgroup.map homomorphism : Set H)).comap homomorphism)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (centralizer_le_comap_centralizer_map homomorphism subgroup)).mpr
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator hconjugator element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro actor hactor
  have hcommutator : ⁅conjugator⁻¹, actor⁆ ∈ homomorphism.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_centralizer_iff.mp
      (((Subgroup.centralizer (subgroup.map homomorphism : Set H)).comap homomorphism).inv_mem
        hconjugator) (homomorphism actor) (Subgroup.mem_map_of_mem homomorphism hactor)).symm
  have hfirst : Commute element ⁅conjugator⁻¹, actor⁆ :=
    Subgroup.mem_center_iff.mp (hcentral hcommutator) element
  have hsecond : Commute element actor :=
    (Subgroup.mem_centralizer_iff.mp helement actor hactor).symm
  have hconjugate : Commute element ((MulAut.conj conjugator⁻¹) actor) := by
    rw [conj_eq_commutatorElement_mul]
    exact hfirst.mul_right hsecond
  have hmapped := hconjugate.map (MulAut.conj conjugator).toMonoidHom
  have hresult : Commute (conjugator * element * conjugator⁻¹) actor := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hmapped
  exact hresult.symm

theorem thetaCoreOf_le_centralizer_of_comap_centralizer_map
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (subgroup : Subgroup G) :
    thetaCoreOf prime
      ((Subgroup.centralizer (subgroup.map homomorphism : Set H)).comap homomorphism) ≤
      Subgroup.centralizer (subgroup : Set G) := by
  let preimage := (Subgroup.centralizer (subgroup.map homomorphism : Set H)).comap homomorphism
  intro element helement
  have hpreimage := thetaCoreOf_le prime preimage helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro actor hactor
  have hmapped : Commute (homomorphism actor) (homomorphism element) :=
    Subgroup.mem_centralizer_iff.mp hpreimage (homomorphism actor)
      (Subgroup.mem_map_of_mem homomorphism hactor)
  exact commute_of_map_commute_central_pKernel_prime_complement prime hprime homomorphism
    hcentral hkernel (thetaCoreOf prime preimage)
    (thetaCoreOf_prime_complement prime hprime preimage) actor element helement hmapped

theorem thetaCoreOf_centralizer_eq_comap_centralizer_map
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (subgroup : Subgroup G) :
    thetaCoreOf prime (Subgroup.centralizer (subgroup : Set G)) =
      thetaCoreOf prime
        ((Subgroup.centralizer (subgroup.map homomorphism : Set H)).comap homomorphism) := by
  have hle := centralizer_le_comap_centralizer_map homomorphism subgroup
  rw [thetaCoreOf_normal_intersection prime hprime _ _ hle
    (centralizer_normal_in_comap_centralizer_map homomorphism hcentral subgroup)]
  exact inf_eq_right.mpr
    (thetaCoreOf_le_centralizer_of_comap_centralizer_map prime hprime homomorphism
      hcentral hkernel subgroup)

theorem thetaCoreOf_map_eq_of_central_kernel {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hcentral : homomorphism.ker ≤ Subgroup.center G) (subgroup : Subgroup G) :
    (thetaCoreOf prime subgroup).map homomorphism =
      thetaCoreOf prime (subgroup.map homomorphism) := by
  let restriction := homomorphism.subgroupMap subgroup
  have hrestrictionCentral : restriction.ker ≤ Subgroup.center subgroup := by
    intro element helement
    have hkernel : (element : G) ∈ homomorphism.ker :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp helement)
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcentral hkernel) other)
  have hmap := solvablePrimeComplementCore_map_eq_of_central_kernel prime hprime
    restriction (homomorphism.subgroupMap_surjective subgroup) hrestrictionCentral
  have hcomposition : (subgroup.map homomorphism).subtype.comp restriction =
      homomorphism.comp subgroup.subtype := by
    ext element
    rfl
  have hresult := congrArg (Subgroup.map (subgroup.map homomorphism).subtype) hmap
  rw [Subgroup.map_map, hcomposition, ← Subgroup.map_map] at hresult
  exact hresult

theorem thetaCoreOf_centralizer_map_eq_of_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hkernel : IsPGroup prime homomorphism.ker) (subgroup : Subgroup G) :
    (thetaCoreOf prime (Subgroup.centralizer (subgroup : Set G))).map homomorphism =
      thetaCoreOf prime (Subgroup.centralizer (subgroup.map homomorphism : Set H)) := by
  rw [thetaCoreOf_centralizer_eq_comap_centralizer_map prime hprime homomorphism
    hcentral hkernel subgroup, thetaCoreOf_map_eq_of_central_kernel prime hprime
    homomorphism hcentral, Subgroup.map_comap_eq_self_of_surjective hsurjective]

theorem prime_complement_disjoint_pSubgroup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (complement pSubgroup : Subgroup G)
    (hcomplement : ¬prime ∣ Nat.card complement) (hpgroup : IsPGroup prime pSubgroup) :
    Disjoint complement pSubgroup := by
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp hpgroup
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hcard]
  exact hprime.coprime_pow_of_not_dvd hcomplement

theorem subgroupMap_injective_of_prime_complement_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hkernel : IsPGroup prime homomorphism.ker) (subgroup : Subgroup G)
    (hcomplement : ¬prime ∣ Nat.card subgroup) :
    Function.Injective (homomorphism.subgroupMap subgroup) := by
  have hdisjoint := prime_complement_disjoint_pSubgroup prime hprime subgroup
    homomorphism.ker hcomplement hkernel
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro element helement
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Subgroup.disjoint_def.mp hdisjoint element.property
  exact congrArg Subtype.val (MonoidHom.mem_ker.mp helement)

theorem thetaCoreOf_centralizer_subgroupMap_bijective_of_central_pKernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hkernel : IsPGroup prime homomorphism.ker) (subgroup : Subgroup G) :
    Function.Bijective
      (homomorphism.subgroupMap (thetaCoreOf prime (Subgroup.centralizer (subgroup : Set G)))) := by
  exact ⟨subgroupMap_injective_of_prime_complement_pKernel prime hprime homomorphism hkernel _
    (thetaCoreOf_prime_complement prime hprime _), homomorphism.subgroupMap_surjective _⟩

theorem solvablePrimeComplementCore_comap_eq_of_central_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G) :
    (solvablePrimeComplementCore H prime).comap homomorphism =
      solvablePrimeComplementCore G prime ⊔ homomorphism.ker := by
  rw [← solvablePrimeComplementCore_map_eq_of_central_kernel prime hprime homomorphism
    hsurjective hcentral, Subgroup.comap_map_eq]

end CFSG.RankThreeEvenClassification.Helpers
