module

public import CFSG.Assembly.OrderReductions.EvenPointNormalizer
public import CFSG.Assembly.OrderReductions.RankOneInduction

public section

namespace CFSG.OrderReductions.RankOneEvenPoint

universe group_universe

open CFSG.OrderReductions.InvolutionGraph

theorem maximal_even_point_normalizer_of_coreFree_centrality
    (centrality : ∀ (group : Type group_universe) [Group group] [Finite group],
      CFSG.OrderReductions.RankOneInduction.NoFourInvolutions group → CFSG.OrderReductions.OddCore.oddCore group = ⊥ →
      ∀ involution : Involution group, involution.val ∈ Subgroup.center group)
    {group : Type group_universe} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_odd : Odd prime) (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup) :
    ∃ point ∈ MulAction.fixedPoints subgroup (Component group),
      Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point)) := by
  classical
  let normalizer := Subgroup.normalizer (subgroup : Set group)
  by_cases four : ∃ first second : Involution normalizer,
      first ≠ second ∧ Commute first.val second.val
  · obtain ⟨first, second, distinct, commutes⟩ := four
    exact CFSG.OrderReductions.EvenPointNormalizer.maximal_exists_even_point_normalizer_of_four_involutions
      prime prime_odd subgroup maximal first second distinct commutes
  · have no_four : CFSG.OrderReductions.RankOneInduction.NoFourInvolutions normalizer := by
      intro first second commutes
      by_contra distinct
      exact four ⟨first, second, distinct, commutes⟩
    let projection := QuotientGroup.mk' (CFSG.OrderReductions.OddCore.oddCore normalizer)
    have odd_kernel : Odd (Nat.card projection.ker) := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.OrderReductions.OddCore.oddCore_odd normalizer
    exact CFSG.OrderReductions.EvenPointNormalizer.maximal_even_point_normalizer_of_central_images
      prime prime_odd subgroup maximal projection (QuotientGroup.mk'_surjective _) odd_kernel no_four
      (CFSG.OrderReductions.RankOneInduction.involution_image_central_of_coreFree_centrality
        centrality normalizer no_four)

theorem maximal_even_point_normalizer_of_proper_normal_step
    (proper_normal_step : ∀ (group : Type group_universe) [Group group] [Finite group],
      CFSG.OrderReductions.RankOneInduction.NoFourInvolutions group → CFSG.OrderReductions.OddCore.oddCore group = ⊥ →
      ∀ involution : Involution group,
        (∃ normal : Subgroup group, normal.Normal ∧ normal ≠ ⊤ ∧ involution.val ∈ normal) ∨
        ∃ sylow : Sylow 2 group, IsCyclic sylow)
    {group : Type group_universe} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_odd : Odd prime) (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup) :
    ∃ point ∈ MulAction.fixedPoints subgroup (Component group),
      Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point)) :=
  maximal_even_point_normalizer_of_coreFree_centrality
    (CFSG.OrderReductions.RankOneInduction.coreFree_centrality_of_proper_normal_step proper_normal_step)
    prime prime_odd subgroup maximal

end CFSG.OrderReductions.RankOneEvenPoint
