module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniStabilityTransfer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableLinearStability

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem solvable_elementary_module_prime_stable_action {actor : Type u} {acted : Type v}
    [Group actor] [Finite actor] [Group.IsSolvable actor] [CommGroup acted] [Finite acted]
    (prime : ℕ) [Fact prime.Prime] [Module (ZMod prime) (Additive acted)] (hodd : Odd prime)
    (action : actor →* MulAut acted) (halternative : 5 ≤ prime ∨ Odd (Nat.card actor)) :
    PrimeStableAction prime action := by
  apply primeStableAction_of_elementary_linear_stability prime action
  exact solvable_linear_prime_stable_action (field := ZMod prime) (space := Additive acted)
    prime Fact.out hodd ((zmodLinearAutomorphisms prime acted).comp action) halternative

theorem solvable_elementary_prime_stable_action {actor : Type u} {acted : Type v}
    [Group actor] [Finite actor] [Group.IsSolvable actor] [CommGroup acted] [Finite acted]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime)
    (hpower : ∀ member : acted, member ^ prime = 1)
    (action : actor →* MulAut acted) (halternative : 5 ≤ prime ∨ Odd (Nat.card actor)) :
    PrimeStableAction prime action := by
  have : Fact prime.Prime := ⟨hprime⟩
  have hkilled : ∀ member : Additive acted, prime • member = 0 := by
    intro member
    exact congrArg Additive.ofMul (hpower (Additive.toMul member))
  let actedModule : Module (ZMod prime) (Additive acted) := AddCommGroup.zmodModule hkilled
  exact solvable_elementary_module_prime_stable_action prime hodd action halternative

theorem solvable_prime_stable_action {actor : Type u} {acted : Type v}
    [Group actor] [Finite actor] [Group.IsSolvable actor] [Group acted] [Finite acted]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) (hpgroup : IsPGroup prime acted)
    (action : actor →* MulAut acted) (halternative : 5 ≤ prime ∨ Odd (Nat.card actor)) :
    PrimeStableAction prime action := by
  have hcommutative : IsMulCommutative (acted ⧸ frattini acted) :=
    pGroup_frattini_quotient_commutative prime hprime hpgroup
  have : IsMulCommutative (acted ⧸ frattini acted) := hcommutative
  let : CommGroup (acted ⧸ frattini acted) := IsMulCommutative.instCommGroup
  have : Finite action.range := Finite.of_surjective action.rangeRestrict action.rangeRestrict_surjective
  have : Group.IsSolvable action.range :=
    Group.isSolvable_of_surjective (f := action.rangeRestrict) action.rangeRestrict_surjective
  apply primeStableAction_of_frattini_image_stability prime hprime hpgroup action
  exact solvable_elementary_prime_stable_action prime hprime hodd
    (pGroup_frattini_quotient_pow_eq_one prime hprime hpgroup)
    ((characteristicQuotientAction (frattini acted)).comp action.range.subtype)
    (halternative.imp_right (odd_card_range_of_odd_domain action))

end CFSG.RankThreeEvenClassification.Helpers
