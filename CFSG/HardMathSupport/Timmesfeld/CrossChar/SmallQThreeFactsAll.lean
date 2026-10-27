module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwoF

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem innerOneBalanceThree_F4_small
    (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ∨ Nat.card K = 4) : InnerOneBalanceThree (adjointGroup Tag.F4 K) :=
  hK.elim innerOneBalanceThree_F4_two innerOneBalanceThree_F4_four

theorem innerOneBalanceThree_E7_small
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    InnerOneBalanceThree (adjointGroup Tag.E7 K) :=
  innerOneBalanceThree_E7_two hK

theorem innerOneBalanceThree_E8_small
    (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ∨ Nat.card K = 4) : InnerOneBalanceThree (adjointGroup Tag.E8 K) :=
  hK.elim innerOneBalanceThree_E8_two innerOneBalanceThree_E8_four

theorem smallQThreeOneBalance_of_E6
    (hE6 : ∀ (K : Type) [Field K] [Finite K], (Nat.card K = 2 ∨ Nat.card K = 4) →
      InnerOneBalanceThree (adjointGroup Tag.E6 K))
    (hTw : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ σ : K ≃+* K,
      (∀ c, σ c = c ^ 2) → InnerOneBalanceThree (twistedE6RootGroup K σ)) :
    SmallQThreeOneBalance :=
  ⟨innerOneBalanceThree_F4_small, hE6, hTw, innerOneBalanceThree_E7_small,
    innerOneBalanceThree_E8_small⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
