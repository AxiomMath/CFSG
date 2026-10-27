module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Two
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Four

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.Blueprint.Chevalley


theorem innerOneBalanceThree_E6_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    InnerOneBalanceThree (adjointGroup .E6 K) := by
  have : CharP K 2 := charP_two_of_card_two_E6 hK
  exact innerOneBalanceThree_E6_two_of_fusion hK (exists_conj_eq_rep_E6_two hK)

theorem innerOneBalanceThree_E6_small : ∀ (K : Type) [Field K] [Finite K],
    (Nat.card K = 2 ∨ Nat.card K = 4) → InnerOneBalanceThree (adjointGroup Tag.E6 K) := by
  intro K _ _ hK
  rcases hK with hK | hK
  · exact innerOneBalanceThree_E6_two hK
  · exact SmallQ3.innerOneBalanceThree_E6_four hK

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
