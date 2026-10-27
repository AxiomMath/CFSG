module

public import CFSG.Assembly.OrderReductions.SolvableOddNormalizer

public section

namespace CFSG.OrderReductions.SolvableOddAuxiliary

universe group_universe

open CFSG.OrderReductions.InvolutionGraph CFSG.OrderReductions.TwoPointInvolutions
open CFSG.OrderReductions.NormalizerAuxiliary CFSG.OrderReductions.PrimeComplementCore

theorem double_transitive_of_minimum_solvable_pair
    {group : Type group_universe} [Group group] [Finite group]
    (induction_hypothesis : ∀ (smaller : Type group_universe) [Group smaller] [Finite smaller],
      Nat.card smaller < Nat.card group →
      ∀ first second : Involution smaller, first ≠ second → Commute first.val second.val →
        ∀ subgroup : Subgroup smaller, StronglyEmbedded subgroup →
          MulAction.IsMultiplyPretransitive smaller (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2)
    (prime : ℕ) [Fact (Nat.Prime prime)] (point : Component group)
    (strong : StronglyEmbedded (componentStabilizer point)) (degree : 3 ≤ Nat.card (Component group))
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup)
    (odd_subgroup : Odd (Nat.card subgroup)) (contains : subgroup ≤ componentStabilizer point)
    (inside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (normalizes : inside.val ∈ Subgroup.normalizer (subgroup : Set group))
    (large : CFSG.OrderReductions.PrimePart.primePart prime (Nat.card (Involution (componentStabilizer point))) ≤
      Nat.card (inversionSet subgroup inside))
    (extension : Subgroup group) (auxiliary : AuxiliaryData point (inversionSet subgroup inside) inside prime extension)
    (outside : Involution group) (outside_extension : outside.val ∈ extension)
    (outside_not_mem : outside.val ∉ componentStabilizer point)
    [Group.IsSolvable (pairSubgroup point ((commutingGraph group).connectedComponentMk outside))]
    (minimum : ∀ competitor : Involution group, competitor.val ∈ extension →
      competitor.val ∉ componentStabilizer point →
        Nat.card (ambientCore prime (pairSubgroup point ((commutingGraph group).connectedComponentMk outside))) ≤
          Nat.card (ambientCore prime (pairSubgroup point ((commutingGraph group).connectedComponentMk competitor))))
    (prime_divides : prime ∣ Nat.card (pairSubgroup point ((commutingGraph group).connectedComponentMk outside)))
    (first second : Involution group) (distinct_involutions : first ≠ second)
    (commutes : Commute first.val second.val)
    (first_mem : first.val ∈ componentStabilizer point)
    (second_mem : second.val ∈ componentStabilizer point)
    (ambient_rule : ∀ other_prime : ℕ, Nat.Prime other_prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) other_prime)
    (normalizer_rule : ∀ normal : Subgroup group,
      normal ≤ pairSubgroup point ((commutingGraph group).connectedComponentMk outside) →
      (normal.subgroupOf (pairSubgroup point ((commutingGraph group).connectedComponentMk outside))).Normal →
      ∀ other_prime : ℕ, Nat.Prime other_prime →
        CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := Subgroup.normalizer (normal : Set group)) other_prime) :
    MulAction.IsMultiplyPretransitive group (Component group) 2 := by
  classical
  let other := (commutingGraph group).connectedComponentMk outside
  have distinct_points : point ≠ other := by
    intro equal
    exact outside_not_mem ((componentStabilizer_involution_iff point outside).mpr equal.symm)
  have equalities := CFSG.OrderReductions.AuxiliaryMinimum.minimum_core_equalities prime point strong subgroup
    prime_group odd_subgroup contains inside inside_mem normalizes large extension auxiliary
    outside outside_extension outside_not_mem minimum
  have regular := CFSG.OrderReductions.AuxiliaryMinimum.pRegular_pair_of_inversion_card prime point other distinct_points
    subgroup prime_group odd_subgroup contains inside inside_mem normalizes
    (auxiliary.2.2 outside outside_extension outside_not_mem).1 large
  obtain ⟨flip, first_moves, second_moves⟩ :=
    CFSG.OrderReductions.InvolutionFusion.involution_swapping_components point other distinct_points
  have other_strong := componentStabilizer_stronglyEmbedded other ⟨point, distinct_points⟩
  have pair_eq : pairSubgroup other point = pairSubgroup point other := inf_comm _ _
  have : Group.IsSolvable (pairSubgroup other point) := by
    rw [pair_eq]
    infer_instance
  have pair_nontrivial : pairSubgroup other point ≠ ⊥ := by
    intro trivial
    have card_one : Nat.card (pairSubgroup point other) = 1 := by
      rw [← pair_eq, trivial, Subgroup.card_bot]
    rw [card_one] at prime_divides
    exact (Fact.out : Nat.Prime prime).not_dvd_one prime_divides
  have conjugate_mem (involution : Involution group) (mem_point : involution.val ∈ componentStabilizer point) :
      (flip.val • involution).val ∈ componentStabilizer other := by
    have mem_image := Subgroup.mem_map_of_mem (MulAut.conj flip.val).toMonoidHom mem_point
    rw [← componentStabilizer_smul, first_moves] at mem_image
    exact mem_image
  apply CFSG.OrderReductions.SolvableOddNormalizer.double_transitive_of_equal_core_solvable_pair
    induction_hypothesis prime other point distinct_points.symm other_strong degree pair_nontrivial
    (flip := flip) (inside := outside) (first := flip.val • first) (second := flip.val • second)
  · rw [pair_eq]
    exact CFSG.OrderReductions.AuxiliaryMinimum.pRegular_pair_symm prime point other distinct_points regular
  · exact second_moves
  · exact first_moves
  · exact involution_mem_componentStabilizer outside
  · simpa only [pairSubgroup, inf_comm] using equalities.2
  · exact fun equal => distinct_involutions (smul_left_cancel flip.val equal)
  · exact commutes.map (MulAut.conj flip.val).toMonoidHom
  · exact conjugate_mem first first_mem
  · exact conjugate_mem second second_mem
  · exact ambient_rule
  · rw [pair_eq]
    exact normalizer_rule

end CFSG.OrderReductions.SolvableOddAuxiliary
