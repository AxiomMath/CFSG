module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RE

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

abbrev oddCoreOf {X : Type*} [Group X] (Y : Subgroup X) : Subgroup X :=
  (pPrimeCore 2 ↥Y).map Y.subtype

abbrev fourT (K : Type) [Field K] : Subgroup (spinGroup (quadOdd 3 K)) :=
  closure {spinZ K, tSeven K}

abbrev qThree (K : Type) [Field K] : spinGroup (quadOdd 3 K) :=
  shortSeven K (upperSL2 1)

abbrev qOne (K : Type) [Field K] : spinGroup (quadOdd 3 K) :=
  (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 1)

@[expose] def F1 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) → 5 ≤ Nat.card K →
    Nat.card ↥(oddCoreOf (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))))) =
        Nat.card K ^ 5 ∧
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ≤
        oddCoreOf (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) ⊔
          (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ⊓
            normalizer (fourT K : Set (spinGroup (quadOdd 3 K))))

end CFSG.ComponentClassification.HarrisLit.T1.S74
