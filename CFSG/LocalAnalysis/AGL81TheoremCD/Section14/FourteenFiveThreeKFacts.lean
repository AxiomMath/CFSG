module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

@[expose] def KFactNineFourRankOneAut : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ (F : Type) [Group F] [Finite F],
    CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p F →
    CFSG.Open.pRank p (⊤ : Subgroup F) ≤ 1 → ¬ 3 ∣ Nat.card (MulAut F)

@[expose] def KFactNineFourStronglyEmbedded : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X],
    CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p ↥(CFSG.generalizedFitting X) →
    ∀ N : Subgroup X, CFSG.RankThree.PartOne.IsStronglyPEmbedded p N →
      (¬ IsSolvable ↥N ∨ 2 ≤ CFSG.Open.pRank 3 ⁅N, N⁆) → CFSG.pPrimeCore 3 ↥N = ⊥

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
