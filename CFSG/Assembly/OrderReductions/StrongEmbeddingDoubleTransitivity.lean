module

public import CFSG.Assembly.OrderReductions.RankOneEvenPoint
public import CFSG.Assembly.OrderReductions.RankOneSimpleReduction
public import CFSG.Assembly.OrderReductions.StrongEmbeddingInductiveStep

public section

namespace CFSG.OrderReductions.StrongEmbeddingDoubleTransitivity

universe group_universe

open CFSG.OrderReductions.InvolutionGraph

theorem double_transitive_of_odd_order_and_rank_one_inputs
    (odd_solvable : ∀ (group : Type group_universe) [Group group] [Finite group],
      Odd (Nat.card group) → Group.IsSolvable group)
    (rank_one : ∀ (group : Type group_universe) [Group group] [Finite group],
      CFSG.OrderReductions.RankOneInduction.NoFourInvolutions group → CFSG.OrderReductions.OddCore.oddCore group = ⊥ →
      ∀ involution : Involution group, involution.val ∈ Subgroup.center group)
    (group : Type group_universe) [Group group] [Finite group]
    (first second : Involution group) (distinct : first ≠ second) (commutes : Commute first.val second.val)
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    MulAction.IsMultiplyPretransitive group (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2 := by
  classical
  generalize cardinality_eq : Nat.card group = cardinality
  induction cardinality using Nat.strong_induction_on generalizing group with
  | h cardinality induction_hypothesis =>
      have even_point : ∀ (group : Type group_universe) [Group group] [Finite group],
          ∀ prime : ℕ, Nat.Prime prime → CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime := by
        intro current current_group current_finite prime prime_is_prime candidate maximal
        have : Fact (Nat.Prime prime) := ⟨prime_is_prime⟩
        have fixed_nonempty : (MulAction.fixedPoints candidate (Component current)).Nonempty := by
          apply Set.nonempty_of_ncard_ne_zero
          have lower := maximal.prop.2
          rw [Nat.card_coe_set_eq] at lower
          omega
        rcases prime_is_prime.eq_two_or_odd' with prime_two | odd_prime
        · have candidate_bot : candidate = ⊥ := by
            have candidate_prime : IsPGroup 2 candidate := prime_two ▸ maximal.prop.1
            have : Fact (Nat.Prime 2) := ⟨by decide⟩
            by_contra nontrivial
            have : Nontrivial candidate := (Subgroup.nontrivial_iff_ne_bot candidate).mpr nontrivial
            obtain ⟨exponent, exponent_positive, cardinality⟩ := candidate_prime.nontrivial_iff_card.mp inferInstance
            have divides : 2 ∣ Nat.card candidate := by
              rw [cardinality]
              exact dvd_pow_self 2 (ne_of_gt exponent_positive)
            obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2
              divides
            let involution : Involution current :=
              ⟨element.val, (Subgroup.orderOf_coe element).trans element_order⟩
            have fixed : ∀ point ∈ MulAction.fixedPoints candidate (Component current),
                point = (commutingGraph current).connectedComponentMk involution := by
              intro other other_fixed
              exact ((componentStabilizer_involution_iff other involution).mp
                (MulAction.mem_fixedPoints.mp other_fixed element)).symm
            have singleton : MulAction.fixedPoints candidate (Component current) ⊆
                {(commutingGraph current).connectedComponentMk involution} := by
              intro other membership
              exact Set.mem_singleton_iff.mpr (fixed other membership)
            have bound := Set.ncard_le_ncard singleton
            rw [Set.ncard_singleton] at bound
            have lower := maximal.prop.2
            rw [Nat.card_coe_set_eq] at lower
            omega
          obtain ⟨point, point_fixed⟩ := fixed_nonempty
          refine ⟨point, point_fixed, ?_⟩
          rw [candidate_bot, Subgroup.normalizer_eq_top, top_inf_eq]
          exact componentStabilizer_even point
        · exact CFSG.OrderReductions.RankOneEvenPoint.maximal_even_point_normalizer_of_coreFree_centrality
            rank_one prime odd_prime candidate maximal
      apply CFSG.OrderReductions.StrongEmbeddingInductiveStep.double_transitive_of_odd_solvable_and_even_point_rules
        (first := first) (second := second) (subgroup := subgroup)
      · intro smaller smaller_group smaller_finite smaller_card smaller_first smaller_second smaller_distinct
          smaller_commutes smaller_subgroup smaller_strong
        exact induction_hypothesis (Nat.card smaller) (by omega) smaller smaller_first smaller_second
          smaller_distinct smaller_commutes smaller_subgroup smaller_strong rfl
      · exact distinct
      · exact commutes
      · exact strong
      · intro candidate candidate_odd
        exact odd_solvable candidate candidate_odd
      · exact even_point group
      · intro normal
        exact even_point (Subgroup.normalizer (normal : Set group))

theorem double_transitive_of_odd_order_and_proper_normal_inputs
    (odd_solvable : ∀ (group : Type group_universe) [Group group] [Finite group],
      Odd (Nat.card group) → Group.IsSolvable group)
    (proper_normal : ∀ (group : Type group_universe) [Group group] [Finite group],
      CFSG.OrderReductions.RankOneInduction.NoFourInvolutions group → CFSG.OrderReductions.OddCore.oddCore group = ⊥ →
      ∀ involution : Involution group,
        (∃ normal : Subgroup group, normal.Normal ∧ normal ≠ ⊤ ∧ involution.val ∈ normal) ∨
        ∃ sylow : Sylow 2 group, IsCyclic sylow)
    (group : Type group_universe) [Group group] [Finite group]
    (first second : Involution group) (distinct : first ≠ second) (commutes : Commute first.val second.val)
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    MulAction.IsMultiplyPretransitive group (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2 :=
  double_transitive_of_odd_order_and_rank_one_inputs odd_solvable
    (CFSG.OrderReductions.RankOneInduction.coreFree_centrality_of_proper_normal_step proper_normal)
    group first second distinct commutes subgroup strong

theorem double_transitive_of_odd_order_and_simple_rank_one_inputs
    (odd_solvable : ∀ (group : Type group_universe) [Group group] [Finite group],
      Odd (Nat.card group) → Group.IsSolvable group)
    (simple_rank_one : ∀ (group : Type group_universe) [Group group] [Finite group]
      [IsSimpleGroup group], ¬ Group.IsSolvable group → Even (Nat.card group) →
        CFSG.OrderReductions.RankOneInduction.NoFourInvolutions group → False)
    (group : Type group_universe) [Group group] [Finite group]
    (first second : Involution group) (distinct : first ≠ second) (commutes : Commute first.val second.val)
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    MulAction.IsMultiplyPretransitive group (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2 :=
  double_transitive_of_odd_order_and_rank_one_inputs odd_solvable
    (CFSG.OrderReductions.RankOneSimpleReduction.coreFree_centrality_of_nonsolvable_simple_rank_one
      simple_rank_one) group first second distinct commutes subgroup strong

end CFSG.OrderReductions.StrongEmbeddingDoubleTransitivity
