module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74FDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

@[expose] def F1Odd : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
    Nat.card ↥(oddCoreOf (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))))) =
        Nat.card K ^ 5 ∧
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ≤
        oddCoreOf (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) ⊔
          (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ⊓
            normalizer (fourT K : Set (spinGroup (quadOdd 3 K))))

@[expose] def F2bOdd : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
    Nat.card K ^ 9 * (Nat.card K ^ 2 - 1) ^ 2 ≤
      Nat.card ↥(centralizer ({qOne K} : Set (spinGroup (quadOdd 3 K))))

@[expose] def F4Odd : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) → ∀ c d : K, c ≠ 0 → d ≠ 0 →
    Nat.card ↥(centralizer ({shortSeven K (upperSL2 c) *
        (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 d)} :
          Set (spinGroup (quadOdd 3 K)))) ≤
      4 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1)

end CFSG.ComponentClassification.HarrisLit.T1.S74
