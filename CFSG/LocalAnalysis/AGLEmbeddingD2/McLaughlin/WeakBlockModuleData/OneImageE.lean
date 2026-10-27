module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairTRFrontier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImage
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowClauseO
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive
import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.BigVector
import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.Fixed
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PermJordan
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def IsAltTwelveOrSixteen (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* alternatingGroup (Fin 12)) ∨ Nonempty (Y ≃* alternatingGroup (Fin 16))

@[expose] def OneImageNonAltResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    ¬ IsAltTwelveOrSixteen ↥(barM M L) →
    ¬ (Open.pRank 3 L = 2 ∧ ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) →
    (∃ x ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), x ≠ 1 ∧
      3 ≤ Open.pRank 3 (Subgroup.centralizer ({x} : Set G) ⊓ M)) ∧
    (∀ y ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), y ≠ 1 →
      3 ∣ Nat.card (M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G))


theorem pairOneImagePure_of_alt
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive)
    {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (h : IsAltTwelveOrSixteen ↥(barM M L)) :
    ∃ x ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), x ≠ 1 ∧
      3 ≤ Open.pRank 3 (Subgroup.centralizer ({x} : Set G) ⊓ M) := by
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have key : ∀ N : ℕ, 12 ≤ N → Nonempty (↥(barM M L) ≃* alternatingGroup (Fin N)) →
      ∃ x ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), x ≠ 1 ∧
        3 ≤ Open.pRank 3 (Subgroup.centralizer ({x} : Set G) ⊓ M) := by
    intro N hN he
    obtain ⟨e⟩ := he
    obtain ⟨x, hx, hx1, hr⟩ :=
      CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.exists_bigVector_of_alt' h86 hnat hctx hL hN e
    refine ⟨x, hx, hx1, hr.trans ?_⟩
    refine CFSG.SectionRank.pRank_mono (by norm_num) ?_
    exact fun g hg => ⟨hg.2, hL.le hg.1⟩
  rcases h with h | h
  · exact key 12 le_rfl h
  · exact key 16 (by norm_num) h

theorem pairOneImageFix_of_alt (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive) {G : Type}
    [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (h : IsAltTwelveOrSixteen ↥(barM M L)) {y : G}
    (hy : y ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H)) :
    3 ∣ Nat.card (M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have key : ∀ N : ℕ, (N = 12 ∨ N = 16) → Nonempty (↥(barM M L) ≃* alternatingGroup (Fin N)) →
      3 ∣ Nat.card (M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
    intro N hN he
    obtain ⟨e⟩ := he
    exact (CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.fixed_of_alt_pair' h86 hJ hnat hctx hL hN e
      hy).trans
      (Subgroup.card_dvd_of_le (by
        intro g hg
        exact ⟨hL.le hg.1, hg.2⟩))
  rcases h with h | h
  · exact key 12 (Or.inl rfl) h
  · exact key 16 (Or.inr rfl) h


theorem not_rankTwo_of_oneImage (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hU : OutU33) (hL5 : OutL5) {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) :
    ¬ (Open.pRank 3 L = 2 ∧ ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) := by
  rintro ⟨hr, hZ⟩
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
  have hnot := hpr.nineThree_not_one h85 hX hL
  have hrow := tightRow_or_L5Two_of_block hLF h418 hL27 hL (hpr.nineThree h93 hL) hnot.1
    hnot.2 (d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair
      hctx.strong hctx.perf L hL) hr hZ
  have ho := clauseO_tightRow hU hL5 hL hrow
  have := three_le_pRank_of_oneImage hpr h84 h86 hX hH hM4 hthree hL hk1 ho hZ
  omega

theorem pairOneImageE_of_residue (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hU : OutU33) (hL5 : OutL5) (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive)
    (hres : OneImageNonAltResidue) :
    PairOneImagePureE ∧ PairOneImageFixE := by
  refine ⟨?_, ?_⟩
  · intro G _ _ P M A H R hctx hev L hL hk1
    by_cases h : IsAltTwelveOrSixteen ↥(barM M L)
    · exact pairOneImagePure_of_alt hnat hctx hL h
    · exact (hres G P M A H R hctx hev L hL hk1 h
        (not_rankTwo_of_oneImage hLF h418 hL27 h93 hD2 hΛ hU hL5 hctx hL hk1)).1
  · intro G _ _ P M A H R hctx hev L hL hk1 y hy hy1
    by_cases h : IsAltTwelveOrSixteen ↥(barM M L)
    · exact pairOneImageFix_of_alt hJ hnat hctx hL h hy
    · exact (hres G P M A H R hctx hev L hL hk1 h
        (not_rankTwo_of_oneImage hLF h418 hL27 h93 hD2 hΛ hU hL5 hctx hL hk1)).2 y hy hy1

end CFSG.AGLEmbeddingD2.McLaughlin
