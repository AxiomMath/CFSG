module

public import CFSG.Assembly.OrderReductions.RankTwoNormalizer
public import CFSG.Assembly.OrderReductions.SmallerNormalizer
public import CFSG.Assembly.OrderReductions.NormalizerTerminal

public section

namespace CFSG.OrderReductions.NormalizerInduction

universe group_universe

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions

theorem double_transitive_of_nontrivial_normal_pair
    {group : Type group_universe} [Group group] [Finite group]
    (induction_hypothesis : ∀ (smaller : Type group_universe) [Group smaller] [Finite smaller],
      Nat.card smaller < Nat.card group →
      ∀ first second : Involution smaller, first ≠ second → Commute first.val second.val →
        ∀ subgroup : Subgroup smaller, StronglyEmbedded subgroup →
          MulAction.IsMultiplyPretransitive smaller (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2)
    (point : Component group) (strong : StronglyEmbedded (componentStabilizer point))
    (degree : 3 ≤ Nat.card (Component group))
    (inside outside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (outside_not_mem : outside.val ∉ componentStabilizer point)
    (normal : Subgroup group) (nontrivial : normal ≠ ⊥)
    (contains : normal ≤ pairSubgroup point (outside.val • point))
    [(normal.subgroupOf (pairSubgroup point (outside.val • point))).Normal]
    (inside_normalizes : inside.val ∈ Subgroup.normalizer (normal : Set group))
    (outside_normalizes : outside.val ∈ Subgroup.normalizer (normal : Set group))
    (first second : Involution group) (distinct_involutions : first ≠ second)
    (commutes : Commute first.val second.val)
    (first_mem : first.val ∈ componentStabilizer point)
    (second_mem : second.val ∈ componentStabilizer point)
    (ambient_rule : ∀ prime : ℕ, Nat.Prime prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (normalizer_rule : ∀ prime : ℕ, Nat.Prime prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule
        (group := Subgroup.normalizer (normal : Set group)) prime) :
    MulAction.IsMultiplyPretransitive group (Component group) 2 := by
  classical
  let normalizer := Subgroup.normalizer (normal : Set group)
  have moves : outside.val • point ≠ point := outside_not_mem
  have all_normalize := CFSG.OrderReductions.NormalizerQuotient.all_point_involutions_normalize
    point (outside.val • point) moves.symm normal contains inside inside_mem inside_normalizes
  have internal_transitive := CFSG.OrderReductions.SmallerNormalizer.two_transitive_of_smaller_quotient
    induction_hypothesis point (outside.val • point) moves.symm strong normal nontrivial contains
    inside outside inside_mem outside_not_mem inside_normalizes outside_normalizes
    first second distinct_involutions commutes first_mem second_mem
  let internal_inside : Involution normalizer :=
    ⟨⟨inside.val, inside_normalizes⟩, by rw [← Subgroup.orderOf_coe]; exact inside.property⟩
  have stabilizer_eq := CFSG.OrderReductions.InternalComponents.stabilizer_intersection_eq_internal
    point strong normalizer all_normalize internal_inside inside_mem
  have pair_le := CFSG.OrderReductions.NormalizerQuotient.pair_le_normalizer
    point (outside.val • point) normal contains
  obtain ⟨prime, prime_is_prime, odd_prime, _, not_regular⟩ :=
    CFSG.OrderReductions.RankTwoNormalizer.exists_nonregular_prime point (outside.val • point) moves.symm
      first second distinct_involutions commutes first_mem second_mem
  have : Fact (Nat.Prime prime) := ⟨prime_is_prime⟩
  obtain ⟨sylow⟩ := Sylow.nonempty (p := prime) (G := pairSubgroup point (outside.val • point))
  let acting : normalizer := ⟨outside.val, outside_normalizes⟩
  obtain ⟨ambient, image_eq⟩ := CFSG.OrderReductions.NormalizerSylow.ambient_sylow_in_normalizer
    prime odd_prime point normalizer internal_inside stabilizer_eq acting moves pair_le
    internal_transitive (normalizer_rule prime prime_is_prime) not_regular sylow
  exact CFSG.OrderReductions.NormalizerTerminal.double_transitive_of_normalizer_sylow
    prime odd_prime (ambient_rule prime prime_is_prime) point (outside.val • point) moves.symm degree
    normalizer all_normalize sylow ambient image_eq not_regular

theorem double_transitive_of_equal_nontrivial_core
    {group : Type group_universe} [Group group] [Finite group]
    (induction_hypothesis : ∀ (smaller : Type group_universe) [Group smaller] [Finite smaller],
      Nat.card smaller < Nat.card group →
      ∀ first second : Involution smaller, first ≠ second → Commute first.val second.val →
        ∀ subgroup : Subgroup smaller, StronglyEmbedded subgroup →
          MulAction.IsMultiplyPretransitive smaller (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2)
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (point other : Component group) (distinct_points : point ≠ other)
    (strong : StronglyEmbedded (componentStabilizer point)) (degree : 3 ≤ Nat.card (Component group))
    (flip inside : Involution group) (first_moves : flip.val • point = other)
    (second_moves : flip.val • other = point) (inside_mem : inside.val ∈ componentStabilizer point)
    (core_eq : CFSG.OrderReductions.PrimeComplementCore.ambientCore prime
      (CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj inside.val) (pairSubgroup point other)) =
        CFSG.OrderReductions.PrimeComplementCore.ambientCore prime (pairSubgroup point other))
    (nontrivial : CFSG.OrderReductions.PrimeComplementCore.ambientCore prime (pairSubgroup point other) ≠ ⊥)
    (first second : Involution group) (distinct_involutions : first ≠ second)
    (commutes : Commute first.val second.val)
    (first_mem : first.val ∈ componentStabilizer point)
    (second_mem : second.val ∈ componentStabilizer point)
    (ambient_rule : ∀ other_prime : ℕ, Nat.Prime other_prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) other_prime)
    (normalizer_rule : ∀ other_prime : ℕ, Nat.Prime other_prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule
        (group := Subgroup.normalizer
          (CFSG.OrderReductions.PrimeComplementCore.ambientCore prime (pairSubgroup point other) : Set group)) other_prime) :
    MulAction.IsMultiplyPretransitive group (Component group) 2 := by
  let normal := CFSG.OrderReductions.PrimeComplementCore.ambientCore prime (pairSubgroup point other)
  have contains : normal ≤ pairSubgroup point (flip.val • point) := by
    rw [first_moves]
    exact CFSG.OrderReductions.PrimeComplementCore.ambientCore_le prime _
  have : (normal.subgroupOf (pairSubgroup point (flip.val • point))).Normal := by
    rw [first_moves]
    exact CFSG.OrderReductions.PrimeComplementCore.ambientCore_normal_in_subgroup prime _
  have inside_normalizes : inside.val ∈ Subgroup.normalizer (normal : Set group) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (CFSG.OrderReductions.RegularCore.core_invariant_of_equal_intersection prime (MulAut.conj inside.val)
        (CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive inside) _ core_eq)
  have flip_normalizes : flip.val ∈ Subgroup.normalizer (normal : Set group) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (CFSG.OrderReductions.RegularCore.ambientCore_invariant prime (MulAut.conj flip.val) _
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (flip_normalizes_pair point other flip first_moves second_moves)))
  have flip_outside : flip.val ∉ componentStabilizer point := by
    intro fixes
    exact distinct_points (fixes.symm.trans first_moves)
  exact double_transitive_of_nontrivial_normal_pair induction_hypothesis point strong degree
    inside flip inside_mem flip_outside normal nontrivial contains inside_normalizes flip_normalizes
    first second distinct_involutions commutes first_mem second_mem ambient_rule normalizer_rule

end CFSG.OrderReductions.NormalizerInduction
