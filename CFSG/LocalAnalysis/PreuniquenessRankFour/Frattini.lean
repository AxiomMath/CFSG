module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem normal_coatom_quotient_isSimpleGroup
    {source : Type u} [Group source]
    (maximal : Subgroup source) [maximal.Normal] (hmaximal : IsCoatom maximal) :
    IsSimpleGroup (source ⧸ maximal) := by
  let : Nontrivial (source ⧸ maximal) := QuotientGroup.nontrivial_iff.mpr hmaximal.ne_top
  constructor
  intro subgroup hnormal
  have hcontained : maximal ≤ subgroup.comap (QuotientGroup.mk' maximal) := by
    intro element helement
    change (QuotientGroup.mk' maximal) element ∈ subgroup
    rw [show (QuotientGroup.mk' maximal) element = 1 from
      (QuotientGroup.eq_one_iff element).mpr helement]
    exact subgroup.one_mem
  by_cases hequal : subgroup.comap (QuotientGroup.mk' maximal) = maximal
  · left
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective maximal)
    rw [hequal]
    ext element
    exact (QuotientGroup.eq_one_iff element).symm
  · right
    have htop : subgroup.comap (QuotientGroup.mk' maximal) = ⊤ :=
      hmaximal.lt_iff.mp (lt_of_le_of_ne hcontained (Ne.symm hequal))
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective maximal)
    rw [htop, Subgroup.comap_top]

theorem pGroup_coatom_quotient_card
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source)
    (maximal : Subgroup source) (hmaximal : IsCoatom maximal) :
    letI := Subgroup.NormalizerCondition.normal_of_coatom maximal
      (by
        let := hgroup.isNilpotent
        exact Group.normalizerCondition_of_isNilpotent) hmaximal
    Nat.card (source ⧸ maximal) = prime := by
  let : Group.IsNilpotent source := hgroup.isNilpotent
  let : maximal.Normal := Subgroup.NormalizerCondition.normal_of_coatom maximal
    Group.normalizerCondition_of_isNilpotent hmaximal
  let : IsSimpleGroup (source ⧸ maximal) :=
    normal_coatom_quotient_isSimpleGroup maximal hmaximal
  have hquotient := hgroup.to_quotient maximal
  let : IsMulCommutative (source ⧸ maximal) :=
    ⟨⟨pGroup_commutative_of_simple prime (Fact.out) hquotient⟩⟩
  have hcardprime : (Nat.card (source ⧸ maximal)).Prime := IsSimpleGroup.prime_card
  rcases hquotient.card_eq_or_dvd with hone | hdivides
  · exact False.elim (hcardprime.ne_one hone)
  · exact (Nat.prime_dvd_prime_iff_eq Fact.out hcardprime).mp hdivides |>.symm

theorem pGroup_pow_mem_frattini
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source)
    (element : source) : element ^ prime ∈ frattini source := by
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro maximal hmaximal
  let : Group.IsNilpotent source := hgroup.isNilpotent
  let : maximal.Normal := Subgroup.NormalizerCondition.normal_of_coatom maximal
    Group.normalizerCondition_of_isNilpotent hmaximal
  have hcard := pGroup_coatom_quotient_card prime hgroup maximal hmaximal
  apply (QuotientGroup.eq_one_iff (element ^ prime)).mp
  change (QuotientGroup.mk' maximal) (element ^ prime) = 1
  rw [map_pow, ← hcard]
  exact pow_card_eq_one'

theorem pGroup_commutator_le_frattini
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source) :
    commutator source ≤ frattini source := by
  unfold frattini Order.radical
  apply le_iInf
  intro maximal
  apply le_iInf
  intro hmaximal
  let : Group.IsNilpotent source := hgroup.isNilpotent
  let : maximal.Normal := Subgroup.NormalizerCondition.normal_of_coatom maximal
    Group.normalizerCondition_of_isNilpotent hmaximal
  let : IsSimpleGroup (source ⧸ maximal) :=
    normal_coatom_quotient_isSimpleGroup maximal hmaximal
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
  exact IsMulCommutative.of_comm
    (pGroup_commutative_of_simple prime Fact.out (hgroup.to_quotient maximal))

theorem pGroup_frattini_quotient_isMulCommutative
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source) :
    IsMulCommutative (source ⧸ frattini source) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (pGroup_commutator_le_frattini prime hgroup)

theorem pGroup_frattini_quotient_pow_eq_one
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hgroup : IsPGroup prime source)
    (element : source ⧸ frattini source) : element ^ prime = 1 := by
  obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (frattini source) element
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (lift ^ prime)).mpr
    (pGroup_pow_mem_frattini prime hgroup lift)

end CFSG.PreuniquenessRankFour.Helpers
