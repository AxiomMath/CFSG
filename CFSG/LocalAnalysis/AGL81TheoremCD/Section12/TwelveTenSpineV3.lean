module

public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteen
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenSpineV2
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankCount
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockTypeLThree

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

structure TwelveTenSpineV3 (M : Subgroup G) (p : ℕ) (Q H : Subgroup G) : Prop where
  h41 : ∀ d : ℕ, d ∈ sigmaSet G M → ¬ d ∣ Nat.card (H ⊓ M : Subgroup G)
  h1015 : TenFifteenSigma M H
  h126 : ∀ (d : ℕ) (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ),
    TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃ → TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃


theorem TwelveTenSpineV3.toV2 {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (hs : TwelveTenSpineV3 M p Q H)
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (h : TwelveCtx G M p Q H) : TwelveTenSpineV2 M p Q H := by
  obtain ⟨-, hk1, hmdL⟩ := blockRank_count h1 h2 h25 h84 hN1 h hs.h41 hs.h1015
  exact ⟨hs.h41, hs.h1015, hmdL, hL3_of_blocks h1 h2 h25 h hk1, hs.h126⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
