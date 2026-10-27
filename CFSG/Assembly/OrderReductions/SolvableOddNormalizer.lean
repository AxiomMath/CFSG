module

public import CFSG.Assembly.OrderReductions.ThompsonSolvableOdd

public section

namespace CFSG.OrderReductions.SolvableOddNormalizer

universe group_universe

open CFSG.OrderReductions.InvolutionGraph CFSG.OrderReductions.TwoPointInvolutions CFSG.OrderReductions.ThompsonCoreProduct

theorem double_transitive_of_equal_core_solvable_pair
    {group : Type group_universe} [Group group] [Finite group]
    (induction_hypothesis : ∀ (smaller : Type group_universe) [Group smaller] [Finite smaller],
      Nat.card smaller < Nat.card group →
      ∀ first second : Involution smaller, first ≠ second → Commute first.val second.val →
        ∀ subgroup : Subgroup smaller, StronglyEmbedded subgroup →
          MulAction.IsMultiplyPretransitive smaller (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2)
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (point other : Component group) (distinct_points : point ≠ other)
    (strong : StronglyEmbedded (componentStabilizer point)) (degree : 3 ≤ Nat.card (Component group))
    [Group.IsSolvable (pairSubgroup point other)]
    (pair_nontrivial : pairSubgroup point other ≠ ⊥)
    (regular : CFSG.OrderReductions.PrimeRegular.PRegular prime (pairSubgroup point other) (componentStabilizer point))
    (flip inside : Involution group) (first_moves : flip.val • point = other)
    (second_moves : flip.val • other = point) (inside_mem : inside.val ∈ componentStabilizer point)
    (core_eq : CFSG.OrderReductions.PrimeComplementCore.ambientCore prime
      (CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj inside.val) (pairSubgroup point other)) =
        CFSG.OrderReductions.PrimeComplementCore.ambientCore prime (pairSubgroup point other))
    (first second : Involution group) (distinct_involutions : first ≠ second)
    (commutes : Commute first.val second.val)
    (first_mem : first.val ∈ componentStabilizer point)
    (second_mem : second.val ∈ componentStabilizer point)
    (ambient_rule : ∀ other_prime : ℕ, Nat.Prime other_prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) other_prime)
    (normalizer_rule : ∀ normal : Subgroup group, normal ≤ pairSubgroup point other →
      (normal.subgroupOf (pairSubgroup point other)).Normal →
      ∀ other_prime : ℕ, Nat.Prime other_prime →
        CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := Subgroup.normalizer (normal : Set group)) other_prime) :
    MulAction.IsMultiplyPretransitive group (Component group) 2 := by
  apply CFSG.OrderReductions.ThompsonNormalizer.double_transitive_of_equal_core_and_independent_product
    induction_hypothesis prime point other distinct_points strong degree pair_nontrivial regular
    flip inside first_moves second_moves inside_mem core_eq first second distinct_involutions commutes
    first_mem second_mem
  · have odd_pair : Odd (Nat.card (pairSubgroup point other)) :=
      distinct_componentStabilizers_odd_intersection point other distinct_points
    intro sylow other_sylow
    rcases (Fact.out : Nat.Prime prime).eq_two_or_odd' with prime_two | odd_prime
    · have core_top : CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime (pairSubgroup point other) = ⊤ := by
        apply top_unique
        apply CFSG.OrderReductions.PrimeComplementCore.normal_le_primeComplementCore prime (⊤ : Subgroup (pairSubgroup point other))
        rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (pairSubgroup point other)) ≃*
          pairSubgroup point other).toEquiv, prime_two]
        exact odd_pair.not_two_dvd_nat
      simp only [coreProduct, core_top, top_sup_eq]
    · exact (CFSG.OrderReductions.ThompsonSolvableOdd.coreProduct_independent_of_solvable_odd
        prime odd_prime odd_pair other_sylow) sylow
  · exact ambient_rule
  · exact normalizer_rule

end CFSG.OrderReductions.SolvableOddNormalizer
