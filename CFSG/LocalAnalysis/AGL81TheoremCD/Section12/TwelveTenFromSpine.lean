module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenSpineV3
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenSylowReduction

import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteenHolds

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12


theorem twelveTenGen_of_spine
    (hs : ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (Q H : Subgroup G),
      TwelveCtx G M p Q H → CFSG.ABGLocalTools.IsSylowOf p Q H → TwelveTenSpine M p Q H) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.TwelveTenGen :=
  twelveTenGen_of_sylow_false fun G _ _ M p Q H h hsyl =>
    h4StarFam_contra_spine h CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved
      CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
      CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds
      (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
          CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved) (hs G M p Q H h hsyl)

theorem twelveTenSpine_of_v2 {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ}
    {Q H : Subgroup G} (h : TwelveCtx G M p Q H)
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour)
    (hv : TwelveTenSpineV2 M p Q H) : TwelveTenSpine M p Q H := by
  obtain ⟨h124, h125, hcard⟩ :=
    twelveFour_twelveFive_of_blocks h h1 h2 h25 h84 hv.h41 hv.h1015 hv.hmdL hv.hL3
  exact twelveTenSpine_of_v2_core h (pRank_three_le_three_of_twelveCtx h h124) hcard h125 hv

theorem twelveTenGen_of_spineV2
    (hs : ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (Q H : Subgroup G),
      TwelveCtx G M p Q H → CFSG.ABGLocalTools.IsSylowOf p Q H → TwelveTenSpineV2 M p Q H) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.TwelveTenGen :=
  twelveTenGen_of_spine fun G _ _ M p Q H h hsyl =>
    twelveTenSpine_of_v2 h CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved
      CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
      CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds
      (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
          CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved) (hs G M p Q H h hsyl)

theorem twelveTenGen_of_spineV3
    (hs : ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (Q H : Subgroup G),
      TwelveCtx G M p Q H → CFSG.ABGLocalTools.IsSylowOf p Q H → TwelveTenSpineV3 M p Q H) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.TwelveTenGen :=
  twelveTenGen_of_spineV2 fun G _ _ M p Q H h hsyl =>
    (hs G M p Q H h hsyl).toV2 CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved
      CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
      CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds
      (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
          CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved)
      CFSG.LocalAnalysis.AGL81I.Section4.agl81FourNineteen_holds h

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
