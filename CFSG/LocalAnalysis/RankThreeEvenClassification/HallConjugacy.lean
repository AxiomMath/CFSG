module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.AbelianComplementConjugacy
public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallTransport

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem hall_conjugacy_of_solvable {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    (primes : Set ℕ) (first second : Subgroup G)
    (hfirst : HallFor primes first) (hsecond : HallFor primes second) :
    ∃ conjugator : G, first.map (MulAut.conj conjugator).toMonoidHom = second := by
  classical
  induction hsize : Nat.card G using Nat.strong_induction_on generalizing G with
  | h size ih =>
    by_cases htrivial : Subsingleton G
    · have : Subsingleton G := htrivial
      refine ⟨1, ?_⟩
      rw [subgroup_map_conj_one]
      exact Subsingleton.elim _ _
    have : Nontrivial G := not_subsingleton_iff_nontrivial.mp htrivial
    obtain ⟨kernel, hminimal⟩ := exists_minimal_nontrivial_normal (G := G)
    have : kernel.Normal := hminimal.1.1
    obtain ⟨kernelPrime, hkernelPrime, _, dimension, _, hkernelCard⟩ :=
      minimal_normal_solvable_elementary kernel hminimal inferInstance
    let quotient := QuotientGroup.mk' kernel
    have hquotientSmall : Nat.card (G ⧸ kernel) < size := by
      rw [← hsize]
      exact quotient_card_lt_of_nontrivial_subgroup kernel hminimal.1.2
    obtain ⟨quotientConjugator, hquotientConjugacy⟩ :=
      ih (Nat.card (G ⧸ kernel)) hquotientSmall
        (G := G ⧸ kernel) (first.map quotient) (second.map quotient)
        (HallFor.map primes first quotient (QuotientGroup.mk'_surjective kernel) hfirst)
        (HallFor.map primes second quotient (QuotientGroup.mk'_surjective kernel) hsecond) rfl
    obtain ⟨firstConjugator, hfirstConjugator⟩ :=
      QuotientGroup.mk'_surjective kernel quotientConjugator
    let adjusted := first.map (MulAut.conj firstConjugator).toMonoidHom
    have hadjusted : HallFor primes adjusted :=
      HallFor.map primes first (MulAut.conj firstConjugator).toMonoidHom
        (MulAut.conj firstConjugator).surjective hfirst
    have hmapEq : adjusted.map quotient = second.map quotient := by
      rw [map_conjugate_subgroup_eq, hfirstConjugator]
      exact hquotientConjugacy
    have hjoinEq : adjusted ⊔ kernel = second ⊔ kernel := by
      have heq := congrArg (fun subgroup : Subgroup (G ⧸ kernel) => subgroup.comap quotient) hmapEq
      simpa only [Subgroup.comap_map_eq, quotient, QuotientGroup.ker_mk'] using heq
    let overgroup := adjusted ⊔ kernel
    have hadjustedLe : adjusted ≤ overgroup := le_sup_left
    have hsecondLe : second ≤ overgroup := by
      change second ≤ adjusted ⊔ kernel
      rw [hjoinEq]
      exact le_sup_left
    have hremaining : ∃ conjugator : G,
        adjusted.map (MulAut.conj conjugator).toMonoidHom = second := by
      by_cases hovergroupNe : overgroup ≠ ⊤
      · have hovergroupSmall : Nat.card overgroup < size := by
          rw [← hsize]
          have hstrict := subgroup_card_lt_of_lt overgroup ⊤ (lt_top_iff_ne_top.mpr hovergroupNe)
          rw [Subgroup.card_top] at hstrict
          exact hstrict
        obtain ⟨conjugator, hconjugacy⟩ := ih (Nat.card overgroup) hovergroupSmall
          (G := overgroup) (adjusted.subgroupOf overgroup) (second.subgroupOf overgroup)
          (HallFor.subgroupOf primes adjusted overgroup hadjustedLe hadjusted)
          (HallFor.subgroupOf primes second overgroup hsecondLe hsecond) rfl
        refine ⟨conjugator, ?_⟩
        have hmapped := congrArg (fun subgroup : Subgroup overgroup => subgroup.map overgroup.subtype)
          hconjugacy
        rw [map_conjugate_subgroup_eq, Subgroup.map_subgroupOf_eq_of_le hadjustedLe,
          Subgroup.map_subgroupOf_eq_of_le hsecondLe] at hmapped
        exact hmapped
      have hovergroupTop : overgroup = ⊤ := not_ne_iff.mp hovergroupNe
      by_cases hkernelMem : kernelPrime ∈ primes
      · have hkernelOrder : PrimeSetOrder primes (Nat.card kernel) := by
          rw [hkernelCard]
          exact PrimeSetOrder.prime_pow primes kernelPrime hkernelPrime hkernelMem dimension
        have hkernelAdjusted := normal_primeSetOrder_le_hall primes kernel adjusted hkernelOrder hadjusted
        have hkernelSecond := normal_primeSetOrder_le_hall primes kernel second hkernelOrder hsecond
        have hadjustedTop : adjusted = ⊤ := by
          calc
            adjusted = adjusted ⊔ kernel := (sup_eq_left.mpr hkernelAdjusted).symm
            _ = ⊤ := hovergroupTop
        have hsecondTop : second = ⊤ := by
          calc
            second = second ⊔ kernel := (sup_eq_left.mpr hkernelSecond).symm
            _ = adjusted ⊔ kernel := hjoinEq.symm
            _ = ⊤ := hovergroupTop
        refine ⟨1, ?_⟩
        rw [subgroup_map_conj_one, hadjustedTop, hsecondTop]
      have hkernelOrder : PrimeSetOrder primesᶜ (Nat.card kernel) := by
        rw [hkernelCard]
        exact PrimeSetOrder.prime_pow primesᶜ kernelPrime hkernelPrime hkernelMem dimension
      have hkernelAdjusted : kernel.IsComplement' adjusted :=
        normal_complement_of_sup_eq_top_and_coprime kernel adjusted
          (by rw [sup_comm]; exact hovergroupTop)
          (PrimeSetOrder.coprime_compl primes _ _ hadjusted.1 hkernelOrder).symm
      have hkernelSecond : kernel.IsComplement' second :=
        normal_complement_of_sup_eq_top_and_coprime kernel second
          (by rw [sup_comm, ← hjoinEq]; exact hovergroupTop)
          (PrimeSetOrder.coprime_compl primes _ _ hsecond.1 hkernelOrder).symm
      have hcoprime : (Nat.card kernel).Coprime kernel.index := by
        rw [hkernelAdjusted.symm.index_eq_card]
        exact (PrimeSetOrder.coprime_compl primes _ _ hadjusted.1 hkernelOrder).symm
      obtain ⟨conjugator, _, hconjugacy⟩ := abelian_normal_complements_conjugate kernel adjusted second
        (minimal_normal_solvable_commutative kernel hminimal inferInstance)
        hkernelAdjusted hkernelSecond hcoprime
      exact ⟨conjugator, hconjugacy⟩
    obtain ⟨secondConjugator, hsecondConjugator⟩ := hremaining
    refine ⟨secondConjugator * firstConjugator, ?_⟩
    rw [subgroup_map_conj_mul]
    exact hsecondConjugator

end CFSG.RankThreeEvenClassification.Helpers
