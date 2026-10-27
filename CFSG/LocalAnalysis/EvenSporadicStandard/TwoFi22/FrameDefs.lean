module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.GolayBasic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open CFSG.EvenSporadicStandard.Wong77.Module

@[expose] def eVec (i : Fin 23) : Multiplicative Word := Multiplicative.ofAdd (Pi.single i 1)

structure GoodFrame (X : Type*) [Group X] where
  φ : Multiplicative Word →* X
  ker_weight : ∀ w : Word, φ (Multiplicative.ofAdd w) = 1 → w = 0 ∨ 7 ≤ hammingNorm w
  prod_ones : φ (Multiplicative.ofAdd allOnes) = 1

namespace GoodFrame

variable {X : Type*} [Group X] (F : GoodFrame X)

@[expose] def pt (i : Fin 23) : X := F.φ (eVec i)

end GoodFrame

@[expose] def goodFrame_of_ker_eq {X : Type*} [Group X] (φ : Multiplicative Word →* X)
    (hker : ∀ w : Word, φ (Multiplicative.ofAdd w) = 1 ↔ w ∈ golayCode) : GoodFrame X where
  φ := φ
  ker_weight w hw := by
    by_cases h0 : w = 0
    · exact Or.inl h0
    · exact Or.inr (le_hammingNorm_of_mem_golayCode w ((hker w).1 hw) h0)
  prod_ones := (hker allOnes).2 allOnes_mem_golayCode

end CFSG.EvenSporadicStandard.TwoFi22
