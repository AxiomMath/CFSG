module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowCensus
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def PairOneImageLieTR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    NineThreeTwo M (pCoreOf 2 H) L → 3 ≤ Open.pRank 3 L →
    ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    IsOneImageList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))

@[expose] def LieOneImageResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    NineThreeTwo M (pCoreOf 2 H) L → 3 ≤ Open.pRank 3 L →
    ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    IsOneImageList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) → False

@[expose] def OneImageLowRankResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    Open.pRank 3 L ≤ 1 → ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) → False

@[expose] def OneImageCentreResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ NineThreeFour M (pCoreOf 2 H) L → False

@[expose] def KFactNineThreeThreeBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → 3 ≤ Open.pRank 3 L → ¬ BlockPLThreeSolv M S L


theorem false_of_oneImage_nineThreeFour (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h4 : NineThreeFour M (pCoreOf 2 H) L) : False := by
  have hpr := hctx.pair
  have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h84 : Asc81bEightFour := asc81bEightFour_of_factorization hfact
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hfact
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hH := hctx.esc.pRank_H
  have hM4 := hctx.esc.four_le_pRank_M hctx.beta
  have hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L := fun L hL =>
    hpr.blockHasThree h85 h86 h93 hX kFactParabolicThree
      (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ) hL
  obtain ⟨ho, hc⟩ := blockRankClauses_nineThreeFour hL h4 (hthree L hL)
  rcases hc with ⟨hZ, -⟩ | ⟨-, hrk, hy⟩
  · rw [card_inf_centralizer_eq_card_center, h4.2.1] at hZ
    exact absurd (dvd_refl 3) hZ
  · exact (hpr.false_of_one_weakSBlock_of_rankTwo h84 h86 hX hH hM4 hthree hL hk1 ho hrk hy).elim

theorem oneImageNonAltResidue_of_census (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hLie : PairOneImageLieTR) (hK3 : KFactNineThreeThreeBig)
    (hres : LieOneImageResidue) (hlow : OneImageLowRankResidue)
    (hcen : OneImageCentreResidue) : OneImageNonAltResidue := by
  intro G _ _ P M A H R hctx hev L hL hk1 hnalt hrk
  exfalso
  by_cases h4 : NineThreeFour M (pCoreOf 2 H) L
  · exact false_of_oneImage_nineThreeFour h93 hD2 hΛ hctx hL hk1 h4
  by_cases hZ : 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)
  · exact hcen G P M A H R hctx hev L hL hk1 hZ h4
  rcases pairBlockCensus hLF h418 hL27 h93 hD2 G P M A H R hctx L hL with
    h | h | h | h | h | h
  · exact h4 h
  · exact hrk ⟨h.1, h.2.1⟩
  · exact hnalt (by
      obtain ⟨-, h12⟩ := h
      exact h12)
  · exact hlow G P M A H R hctx hev L hL hk1 h hZ
  · obtain ⟨h23, hr3⟩ := h
    rcases h23 with h2 | h3
    · exact hres G P M A H R hctx hev L hL hk1 h2 hr3 hZ
        (hLie G P M A H R hctx hev L hL hk1 h2 hr3 hZ)
    · have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
      have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hfact
      have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
      exact hK3 G M (pCoreOf 2 H) L hctx.pair.isKGroup.1 hctx.pair.asc81bHyp hL
        (hctx.pair.nineThree_not_one h85 hX hL).1 (hctx.pair.not_isSylowTwoOf_inf h85 hX hL) h3 hr3
        (d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair
          hctx.strong hctx.perf L hL)
  · exact hZ h.1

theorem pairOneImageE_of_census (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hU : OutU33) (hL5 : OutL5) (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive)
    (hLie : PairOneImageLieTR) (hK3 : KFactNineThreeThreeBig)
    (hres : LieOneImageResidue) (hlow : OneImageLowRankResidue)
    (hcen : OneImageCentreResidue) : PairOneImagePureE ∧ PairOneImageFixE :=
  pairOneImageE_of_residue hLF h418 hL27 h93 hD2 hΛ hU hL5 hJ hnat
    (oneImageNonAltResidue_of_census hLF h418 hL27 h93 hD2 hΛ hLie hK3 hres hlow hcen)

theorem pairOneImagePureE_of_census (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hU : OutU33) (hL5 : OutL5) (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive)
    (hLie : PairOneImageLieTR) (hK3 : KFactNineThreeThreeBig)
    (hres : LieOneImageResidue) (hlow : OneImageLowRankResidue)
    (hcen : OneImageCentreResidue) : PairOneImagePureE :=
  (pairOneImageE_of_census hLF h418 hL27 h93 hD2 hΛ hU hL5 hJ hnat hLie hK3 hres hlow hcen).1

theorem pairOneImageFixE_of_census (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hU : OutU33) (hL5 : OutL5) (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive)
    (hLie : PairOneImageLieTR) (hK3 : KFactNineThreeThreeBig)
    (hres : LieOneImageResidue) (hlow : OneImageLowRankResidue)
    (hcen : OneImageCentreResidue) : PairOneImageFixE :=
  (pairOneImageE_of_census hLF h418 hL27 h93 hD2 hΛ hU hL5 hJ hnat hLie hK3 hres hlow hcen).2

end CFSG.AGLEmbeddingD2.McLaughlin
