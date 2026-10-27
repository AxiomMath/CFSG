module

public import CFSG.Assembly.OrderReductions.PointMaximal
public import CFSG.Assembly.OrderReductions.MaximalNormalizerAction

public section

namespace CFSG.OrderReductions.PointMaximalComplete

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions
open CFSG.OrderReductions.FixedNormalizerAction

theorem point_maximal_global_and_even {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (point : Component group) (subgroup : Subgroup group)
    (maximal : Maximal (CFSG.OrderReductions.PointMaximal.PointThreePointPrime prime point) subgroup) :
    Maximal (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup ∧
      Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point)) := by
  classical
  by_cases no_regular : CFSG.OrderReductions.EmptyRegularity.NoRegularPair (group := group) prime
  · have degree : 3 ≤ Nat.card (Component group) := maximal.prop.1.2.trans
      (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)
    have two_transitive := CFSG.OrderReductions.EmptyRegularity.no_regular_double_transitive prime
      even_point_rule no_regular degree
    have generic_maximal : Maximal (CFSG.OrderReductions.MaximalNormalizerAction.PointThreePointPrime prime point) subgroup := maximal
    have global_maximal := CFSG.OrderReductions.MaximalNormalizerAction.maximal_global_of_two_transitive
      prime two_transitive point subgroup generic_maximal
    refine ⟨global_maximal, ?_⟩
    let normalizer := Subgroup.normalizer (subgroup : Set group)
    let := fixedPointAction (points := Component group) subgroup
    have : MulAction.IsMultiplyPretransitive normalizer (MulAction.fixedPoints subgroup (Component group)) 2 :=
      CFSG.OrderReductions.MaximalNormalizerAction.maximal_normalizer_two_transitive prime two_transitive point subgroup generic_maximal
    have one_transitive : MulAction.IsMultiplyPretransitive normalizer
        (MulAction.fixedPoints subgroup (Component group)) 1 :=
      MulAction.isMultiplyPretransitive_of_le (by decide : 1 ≤ 2) (by have := maximal.prop.1.2; omega)
    have : MulAction.IsPretransitive normalizer (MulAction.fixedPoints subgroup (Component group)) :=
      MulAction.is_one_pretransitive_iff.mp one_transitive
    obtain ⟨base, base_fixed, base_even⟩ := even_point_rule subgroup global_maximal
    let source : MulAction.fixedPoints subgroup (Component group) := ⟨base, base_fixed⟩
    let target : MulAction.fixedPoints subgroup (Component group) :=
      ⟨point, MulAction.mem_fixedPoints.mpr fun element => maximal.prop.2 element.property⟩
    obtain ⟨acting, moves⟩ := MulAction.exists_smul_eq normalizer source target
    have point_card := CFSG.OrderReductions.LocalRegularity.normalizer_point_card_conjugate subgroup base point
      acting.val acting.property (congrArg Subtype.val moves)
    exact point_card ▸ base_even
  · have regular_exists : ∃ first second : Component group, first ≠ second ∧
        CFSG.OrderReductions.PrimeRegular.PRegular prime (pairSubgroup first second) (componentStabilizer first) := by
      by_contra missing
      apply no_regular
      intro first second distinct regular
      exact missing ⟨first, second, distinct, regular⟩
    obtain ⟨first, second, distinct, regular⟩ := regular_exists
    have no_two := CFSG.OrderReductions.PointMaximal.no_fixed_two_of_regular prime odd_prime even_point_rule
      first second distinct regular
    exact ⟨(CFSG.OrderReductions.PointMaximal.point_maximal_global_of_no_fixed_two prime point subgroup maximal no_two).1,
      CFSG.OrderReductions.PointMaximal.point_maximal_even_of_no_fixed_two prime even_point_rule point subgroup maximal no_two⟩

end CFSG.OrderReductions.PointMaximalComplete
