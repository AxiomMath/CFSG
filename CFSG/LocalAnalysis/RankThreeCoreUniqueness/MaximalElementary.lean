module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SolvableConstraint
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.NonsolvableSections

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem elementary_centralizing_order_prime_extension
    {G : Type*} [Group G] (prime : ℕ) (elementaryGroup : Subgroup G)
    (helementary : IsElemAbelian prime elementaryGroup) (element : G)
    (hcentralizes : element ∈ Subgroup.centralizer (elementaryGroup : Set G))
    (horder : orderOf element = prime) :
    IsElemAbelian prime (Subgroup.closure ((elementaryGroup : Set G) ∪ {element})) := by
  let : IsMulCommutative elementaryGroup := helementary.1
  let extendedGroup := Subgroup.closure ((elementaryGroup : Set G) ∪ {element})
  have hcommutative : IsMulCommutative extendedGroup := by
    apply CFSG.subgroup_isMulCommutative_closure
    intro first hfirst second hsecond
    rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
    · exact isMulCommutative_iff_of_setLike.mp helementary.1 first hfirst second hsecond
    · obtain rfl := Set.mem_singleton_iff.mp hsecond
      exact Subgroup.mem_centralizer_iff.mp hcentralizes first hfirst
    · obtain rfl := Set.mem_singleton_iff.mp hfirst
      exact (Subgroup.mem_centralizer_iff.mp hcentralizes second hsecond).symm
    · obtain rfl := Set.mem_singleton_iff.mp hfirst
      obtain rfl := Set.mem_singleton_iff.mp hsecond
      rfl
  refine ⟨hcommutative, ?_⟩
  intro value hvalue
  induction hvalue using Subgroup.closure_induction with
  | mem value hvalue =>
    rcases hvalue with hvalue | hvalue
    · exact helementary.2 value hvalue
    · have hvalueEq : value = element := Set.mem_singleton_iff.mp hvalue
      rw [hvalueEq, ← horder]
      exact pow_orderOf_eq_one _
  | one => exact one_pow prime
  | mul first second hfirst hsecond hfirstPower hsecondPower =>
    have hcommute : Commute first second := isMulCommutative_iff_of_setLike.mp
      hcommutative first hfirst second hsecond
    rw [hcommute.mul_pow, hfirstPower, hsecondPower, one_mul]
  | inv value _hvalue hpower => rw [inv_pow, hpower, inv_one]

theorem maximal_elementary_contains_order_prime_centralizer_elements
    {G : Type*} [Group G] (prime : ℕ) (overgroup elementaryGroup : Subgroup G)
    (hcontained : elementaryGroup ≤ overgroup) (helementary : IsElemAbelian prime elementaryGroup)
    (hmaximal : ∀ largerGroup : Subgroup G, largerGroup ≤ overgroup →
      IsElemAbelian prime largerGroup → elementaryGroup ≤ largerGroup →
      largerGroup = elementaryGroup) :
    ∀ element : G, element ∈ overgroup →
      element ∈ Subgroup.centralizer (elementaryGroup : Set G) →
      orderOf element = prime → element ∈ elementaryGroup := by
  intro element helement hcentralizes horder
  let extendedGroup := Subgroup.closure ((elementaryGroup : Set G) ∪ {element})
  have hextendedLe : extendedGroup ≤ overgroup := by
    apply (Subgroup.closure_le overgroup).mpr
    rintro value (hvalue | hvalue)
    · exact hcontained hvalue
    · obtain rfl := Set.mem_singleton_iff.mp hvalue
      exact helement
  have hbaseLe : elementaryGroup ≤ extendedGroup := by
    intro value hvalue
    exact Subgroup.subset_closure (Or.inl hvalue)
  have hequal := hmaximal extendedGroup hextendedLe
    (elementary_centralizing_order_prime_extension prime elementaryGroup helementary
      element hcentralizes horder) hbaseLe
  rw [← hequal]
  exact Subgroup.subset_closure (Or.inr (Set.mem_singleton element))

theorem elementary_full_rank_is_maximal
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (overgroup elementaryGroup : Subgroup G) (_helementary : IsElemAbelian prime elementaryGroup)
    (hcard : Nat.card elementaryGroup = prime ^ pRank prime overgroup) :
    ∀ largerGroup : Subgroup G, largerGroup ≤ overgroup →
      IsElemAbelian prime largerGroup → elementaryGroup ≤ largerGroup →
      largerGroup = elementaryGroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  intro largerGroup hlargerLe hlargerElementary hbaseLe
  obtain ⟨exponent, hlargerCard⟩ := IsPGroup.iff_card.mp
    (elementary_isPGroup prime largerGroup hlargerElementary)
  have hexponent : exponent ≤ pRank prime overgroup := by
    exact le_csSup (pRank_set_bddAbove prime hprime.one_lt overgroup)
      ⟨largerGroup, hlargerLe, hlargerElementary, hlargerCard⟩
  have hcardLe : Nat.card largerGroup ≤ Nat.card elementaryGroup := by
    rw [hlargerCard, hcard]
    exact Nat.pow_le_pow_right hprime.pos hexponent
  have hequalCard : Nat.card elementaryGroup = Nat.card largerGroup :=
    le_antisymm (Subgroup.card_le_of_le hbaseLe) hcardLe
  have hinternalCard : Nat.card (elementaryGroup.subgroupOf largerGroup) = Nat.card largerGroup :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbaseLe).toEquiv).trans hequalCard
  have htop := (elementaryGroup.subgroupOf largerGroup).card_eq_iff_eq_top.mp hinternalCard
  apply le_antisymm
  · intro value hvalue
    have hinternal : (⟨value, hvalue⟩ : largerGroup) ∈ elementaryGroup.subgroupOf largerGroup := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hinternal
  · exact hbaseLe

theorem elementary_full_rank_contains_order_prime_centralizer_elements
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (overgroup elementaryGroup : Subgroup G) (hcontained : elementaryGroup ≤ overgroup)
    (helementary : IsElemAbelian prime elementaryGroup)
    (hcard : Nat.card elementaryGroup = prime ^ pRank prime overgroup) :
    ∀ element : G, element ∈ overgroup →
      element ∈ Subgroup.centralizer (elementaryGroup : Set G) →
      orderOf element = prime → element ∈ elementaryGroup :=
  maximal_elementary_contains_order_prime_centralizer_elements prime overgroup elementaryGroup
    hcontained helementary (elementary_full_rank_is_maximal prime hprime overgroup elementaryGroup
      helementary hcard)

theorem maximal_elementary_prime_constraint_signalizer_le_core
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (overgroup elementaryGroup signalizer : Subgroup G)
    (hconstraint : HasPrimeConstraint (G := overgroup) prime)
    (hcontained : elementaryGroup ≤ overgroup) (helementary : IsElemAbelian prime elementaryGroup)
    (hmaximal : ∀ largerGroup : Subgroup G, largerGroup ≤ overgroup →
      IsElemAbelian prime largerGroup → elementaryGroup ≤ largerGroup →
      largerGroup = elementaryGroup)
    (hsignalizer : prime.Coprime (Nat.card signalizer)) (hsignalizerLe : signalizer ≤ overgroup)
    (hinvariant : elementaryGroup ≤ Subgroup.normalizer (signalizer : Set G)) :
    signalizer ≤ Subgroup.map overgroup.subtype (primeComplementCore prime) :=
  ambient_prime_constraint_signalizer_le_core prime hprime hodd overgroup elementaryGroup signalizer
    hconstraint (elementary_isPGroup prime elementaryGroup helementary) hcontained hsignalizer
    hsignalizerLe hinvariant
    (maximal_elementary_contains_order_prime_centralizer_elements prime overgroup elementaryGroup
      hcontained helementary hmaximal)

theorem elementary_full_rank_maximal_pair_transitive_of_prime_constraint
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (overgroup elementaryGroup first second : Subgroup G)
    (hconstraint : HasPrimeConstraint (G := overgroup) prime)
    (hcontained : elementaryGroup ≤ overgroup) (helementary : IsElemAbelian prime elementaryGroup)
    (hcard : Nat.card elementaryGroup = prime ^ pRank prime overgroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup elementaryGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup elementaryGroup second)
    (hfirstLe : first ≤ overgroup) (hsecondLe : second ≤ overgroup) :
    ∃ conjugator : G, conjugator ∈ Subgroup.centralizer (elementaryGroup : Set G) ∧
      first.map (MulAut.conj conjugator).toMonoidHom = second :=
  rank_two_maximal_pair_transitive_of_prime_constraint prime hprime hodd
    elementaryGroup first second overgroup (elementary_isPGroup prime elementaryGroup helementary)
    hcontained hfirst hsecond hfirstLe hsecondLe hconstraint
    (elementary_full_rank_contains_order_prime_centralizer_elements prime hprime
      overgroup elementaryGroup hcontained helementary hcard)

theorem elementary_full_rank_nontransitive_pair_obstruction
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (overgroup elementaryGroup first second : Subgroup G)
    (hcontained : elementaryGroup ≤ overgroup) (helementary : IsElemAbelian prime elementaryGroup)
    (hcard : Nat.card elementaryGroup = prime ^ pRank prime overgroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup elementaryGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup elementaryGroup second)
    (hfirstLe : first ≤ overgroup) (hsecondLe : second ≤ overgroup)
    (hnontransitive : ¬ ∃ conjugator : G,
      conjugator ∈ Subgroup.centralizer (elementaryGroup : Set G) ∧
        first.map (MulAut.conj conjugator).toMonoidHom = second) :
    ¬ HasPrimeConstraint (G := overgroup) prime ∧
      ¬ Group.IsSolvable overgroup ∧
      ¬ Group.IsSolvable (Subgroup.centralizer
        (pCore prime (overgroup ⧸ primeComplementCore prime) :
          Set (overgroup ⧸ primeComplementCore prime))) := by
  have hnotConstraint : ¬ HasPrimeConstraint (G := overgroup) prime := by
    intro hconstraint
    exact hnontransitive (elementary_full_rank_maximal_pair_transitive_of_prime_constraint
      prime hprime hodd overgroup elementaryGroup first second hconstraint hcontained
      helementary hcard hfirst hsecond hfirstLe hsecondLe)
  refine ⟨hnotConstraint, ?_,
    not_prime_constrained_has_nonsolvable_core_centralizer prime hprime hnotConstraint⟩
  intro hsolvable
  let : Group.IsSolvable overgroup := hsolvable
  exact hnotConstraint (solvable_hasPrimeConstraint prime hprime)

theorem kProper_elementary_full_rank_nontransitive_pair_has_simple_section
    {G : Type*} [Group G] [Finite G] (hK : IsKProperByOrder G)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (overgroup elementaryGroup first second : Subgroup G) (hproper : overgroup ≠ ⊤)
    (hcontained : elementaryGroup ≤ overgroup) (helementary : IsElemAbelian prime elementaryGroup)
    (hcard : Nat.card elementaryGroup = prime ^ pRank prime overgroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup elementaryGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup elementaryGroup second)
    (hfirstLe : first ≤ overgroup) (hsecondLe : second ≤ overgroup)
    (hnontransitive : ¬ ∃ conjugator : G,
      conjugator ∈ Subgroup.centralizer (elementaryGroup : Set G) ∧
        first.map (MulAut.conj conjugator).toMonoidHom = second) :
    ∃ sectionGroup : Subgroup G, sectionGroup ≤ overgroup ∧ Group.IsPerfect sectionGroup ∧
      ∃ kernelGroup : Subgroup sectionGroup, ∃ hnormal : kernelGroup.Normal, letI := hnormal;
        IsSimpleGroup (sectionGroup ⧸ kernelGroup) ∧
        (∃ first second : sectionGroup ⧸ kernelGroup, first * second ≠ second * first) ∧
        Nat.card (sectionGroup ⧸ kernelGroup) ∈ knownSimpleOrders := by
  have hobstruction := elementary_full_rank_nontransitive_pair_obstruction prime hprime hodd
    overgroup elementaryGroup first second hcontained helementary hcard hfirst hsecond
    hfirstLe hsecondLe hnontransitive
  exact kProper_nonsolvable_overgroup_has_simple_section hK overgroup hproper hobstruction.2.1

end CFSG.RankThreeCoreUniqueness.Helpers
