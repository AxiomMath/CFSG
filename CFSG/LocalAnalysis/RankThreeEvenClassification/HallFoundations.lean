module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

@[expose] def PrimeSetOrder (primes : Set ℕ) (order : ℕ) : Prop :=
  ∀ prime : ℕ, prime.Prime → prime ∣ order → prime ∈ primes

@[expose] def HallFor {G : Type u} [Group G] (primes : Set ℕ) (subgroup : Subgroup G) : Prop :=
  PrimeSetOrder primes (Nat.card subgroup) ∧ PrimeSetOrder primesᶜ subgroup.index

theorem PrimeSetOrder.one (primes : Set ℕ) : PrimeSetOrder primes 1 := by
  intro prime hprime hdiv
  exact False.elim (hprime.not_dvd_one hdiv)

theorem PrimeSetOrder.of_dvd (primes : Set ℕ) (first second : ℕ)
    (hsecond : PrimeSetOrder primes second) (hdiv : first ∣ second) : PrimeSetOrder primes first := by
  intro prime hprime hprimeDiv
  exact hsecond prime hprime (hprimeDiv.trans hdiv)

theorem PrimeSetOrder.mul (primes : Set ℕ) (first second : ℕ)
    (hfirst : PrimeSetOrder primes first) (hsecond : PrimeSetOrder primes second) :
    PrimeSetOrder primes (first * second) := by
  intro prime hprime hdiv
  exact (hprime.dvd_mul.mp hdiv).elim (hfirst prime hprime) (hsecond prime hprime)

theorem PrimeSetOrder.prime_pow (primes : Set ℕ) (prime : ℕ) (hprime : prime.Prime)
    (hmem : prime ∈ primes) (dimension : ℕ) : PrimeSetOrder primes (prime ^ dimension) := by
  intro divisor hdivisor hdiv
  have heq : divisor = prime := Nat.prime_eq_prime_of_dvd_pow hdivisor hprime hdiv
  exact heq.symm ▸ hmem

theorem PrimeSetOrder.coprime_compl (primes : Set ℕ) (first second : ℕ)
    (hfirst : PrimeSetOrder primes first) (hsecond : PrimeSetOrder primesᶜ second) :
    first.Coprime second := by
  apply Nat.coprime_of_dvd
  intro prime hprime hdivFirst hdivSecond
  exact hsecond prime hprime hdivSecond (hfirst prime hprime hdivFirst)

theorem HallFor.top_of_primeSetOrder {G : Type u} [Group G]
    (primes : Set ℕ) (horder : PrimeSetOrder primes (Nat.card G)) : HallFor primes (⊤ : Subgroup G) := by
  refine ⟨?_, ?_⟩
  · simpa only [Subgroup.card_top] using horder
  · simpa only [Subgroup.index_top] using PrimeSetOrder.one primesᶜ

theorem HallFor.map_subtype {G : Type u} [Group G]
    (primes : Set ℕ) (overgroup : Subgroup G) (subgroup : Subgroup overgroup)
    (hhall : HallFor primes subgroup) (hindex : PrimeSetOrder primesᶜ overgroup.index) :
    HallFor primes (subgroup.map overgroup.subtype) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective overgroup.subtype_injective]
    exact hhall.1
  · rw [Subgroup.index_map_subtype]
    exact PrimeSetOrder.mul primesᶜ _ _ hhall.2 hindex

theorem quotient_card_lt_of_nontrivial_subgroup {G : Type u} [Group G] [Finite G]
    (subgroup : Subgroup G) (hne : subgroup ≠ ⊥) : Nat.card (G ⧸ subgroup) < Nat.card G := by
  have hcardPos : 0 < Nat.card subgroup := Nat.card_pos
  have hcardNe : Nat.card subgroup ≠ 1 := fun heq => hne (Subgroup.card_eq_one.mp heq)
  have hquotientPos : 0 < Nat.card (G ⧸ subgroup) := Nat.card_pos
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup subgroup]
  have hcardLarge : 1 < Nat.card subgroup := by omega
  nlinarith

theorem hall_exists_of_solvable {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    (primes : Set ℕ) : ∃ subgroup : Subgroup G, HallFor primes subgroup := by
  classical
  induction hsize : Nat.card G using Nat.strong_induction_on generalizing G with
  | h size ih =>
    by_cases htrivial : Subsingleton G
    · have : Subsingleton G := htrivial
      refine ⟨⊤, HallFor.top_of_primeSetOrder primes ?_⟩
      intro prime hprime hdiv
      have hone : Nat.card G = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
      exact False.elim (hprime.not_dvd_one (hone ▸ hdiv))
    have : Nontrivial G := not_subsingleton_iff_nontrivial.mp htrivial
    obtain ⟨kernel, hminimal⟩ := exists_minimal_nontrivial_normal (G := G)
    have : kernel.Normal := hminimal.1.1
    obtain ⟨kernelPrime, hkernelPrime, _, dimension, _, hkernelCard⟩ :=
      minimal_normal_solvable_elementary kernel hminimal inferInstance
    let quotient := QuotientGroup.mk' kernel
    have hquotientSmall : Nat.card (G ⧸ kernel) < size := by
      rw [← hsize]
      exact quotient_card_lt_of_nontrivial_subgroup kernel hminimal.1.2
    obtain ⟨quotientHall, hquotientHall⟩ := ih (Nat.card (G ⧸ kernel)) hquotientSmall
      (G := G ⧸ kernel) rfl
    let overgroup := quotientHall.comap quotient
    have hovergroupIndex : PrimeSetOrder primesᶜ overgroup.index := by
      rw [Subgroup.index_comap_of_surjective quotientHall (QuotientGroup.mk'_surjective kernel)]
      exact hquotientHall.2
    by_cases hovergroupNe : overgroup ≠ ⊤
    · have hovergroupSmall : Nat.card overgroup < size := by
        rw [← hsize]
        have hstrict := subgroup_card_lt_of_lt overgroup ⊤ (lt_top_iff_ne_top.mpr hovergroupNe)
        rw [Subgroup.card_top] at hstrict
        exact hstrict
      obtain ⟨subgroup, hhall⟩ := ih (Nat.card overgroup) hovergroupSmall (G := overgroup) rfl
      exact ⟨subgroup.map overgroup.subtype, HallFor.map_subtype primes overgroup subgroup hhall hovergroupIndex⟩
    have hovergroupTop : overgroup = ⊤ := not_ne_iff.mp hovergroupNe
    have hquotientTop : quotientHall = ⊤ := by
      have hmapped : overgroup.map quotient = quotientHall :=
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective kernel) quotientHall
      rw [hovergroupTop] at hmapped
      have htopMap : (⊤ : Subgroup G).map quotient = ⊤ := by
        rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective kernel)]
      exact (htopMap.symm.trans hmapped).symm
    have hquotientOrder : PrimeSetOrder primes (Nat.card (G ⧸ kernel)) := by
      have horder := hquotientHall.1
      rw [hquotientTop, Subgroup.card_top] at horder
      exact horder
    by_cases hkernelMem : kernelPrime ∈ primes
    · refine ⟨⊤, HallFor.top_of_primeSetOrder primes ?_⟩
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup kernel, hkernelCard]
      exact PrimeSetOrder.mul primes _ _ hquotientOrder
        (PrimeSetOrder.prime_pow primes kernelPrime hkernelPrime hkernelMem dimension)
    have hkernelOrder : PrimeSetOrder primesᶜ (Nat.card kernel) := by
      rw [hkernelCard]
      exact PrimeSetOrder.prime_pow primesᶜ kernelPrime hkernelPrime hkernelMem dimension
    have hcoprime : (Nat.card kernel).Coprime kernel.index := by
      rw [Subgroup.index_eq_card]
      exact (PrimeSetOrder.coprime_compl primes _ _ hquotientOrder hkernelOrder).symm
    obtain ⟨subgroup, hcomplement⟩ := Subgroup.exists_right_complement'_of_coprime hcoprime
    refine ⟨subgroup, ?_, ?_⟩
    · rw [← hcomplement.symm.index_eq_card, Subgroup.index_eq_card]
      exact hquotientOrder
    · rw [hcomplement.index_eq_card]
      exact hkernelOrder

end CFSG.RankThreeEvenClassification.Helpers
