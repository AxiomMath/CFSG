module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1Stmt

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsLThreeTwo)

@[expose] def K89Sp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    ∀ N L : Subgroup X, CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 N →
      CFSG.Open.pRank 3 N ≤ 1 → L ≤ N → IsLThreeTwoPow (↥L ⧸ CFSG.pCore 2 ↥L) →
      ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ ∧ S ≤ N ∧
        Subgroup.normalizer (S : Set X) ≤ N

@[expose] def KFactL32SimpleNormalizer : Prop :=
  F1L3Odd ∧ F1U3Odd

@[expose] def KFactL32OddFix : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLThreeTwo (Y ⧸ CFSG.pCore 2 Y) →
    ∀ a : Y, orderOf a = 3 → ∀ S : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ →
    ∀ (I : Type) [Group I] [Finite I], (∀ x y : I, x * y = y * x) →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∀ x : I, x ^ p = 1) →
      ∀ ρ : Y →* MulAut I, (∀ x : I, ρ a x = x → x = 1) →
        ∀ x : I, (∀ s ∈ S, ρ s x = x) → x = 1

end CFSG.LocalAnalysis.RankThreeUC.S15
