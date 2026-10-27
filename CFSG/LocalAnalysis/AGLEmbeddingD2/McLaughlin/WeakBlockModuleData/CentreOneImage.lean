module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentrePL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageCensus
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactCentreBlockPLRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), IsWeakSBlock M S L →
    NineThreeConclusion M S L → ¬ NineThreeOne L →
    (NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) → BlockPLThreeSolv M S L →
    barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) →
    3 ≤ Open.pRank 3 (barM M (Subgroup.normalizer (S : Set G) ⊓ L))

@[expose] def OneImageCentreResidueNotA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ NineThreeFour M (pCoreOf 2 H) L →
    ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) → False


theorem false_of_oneImage_centre_alt_six (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hK : KFactBlockCentrePLRank) {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (hZ : 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (e : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) : False := by
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
  have ho : ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      IsPGroup 3 (Subgroup.zpowers u) →
        u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    clauseO_of_cover hL.le hL.perfect (autThreePowInner_alt_of_five_le (N := 6) (by norm_num)) e
  have hrank : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      E ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      IsElemAbelian 3 E →
      Open.pRank 3 E ≤ Open.pRank 3 (E ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) + 2 := by
    intro E hEN hEA _
    refine pRank_le_pRank_inf_centralizer_add_of_cover Nat.prime_three hEN hEA ?_
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
    have := pRank_three_alternating_le (N := 6)
    simpa using this
  have hy := pairBlockCentreThree_of_cited h93 hD2 hK G P M A H R hctx L hL hZ
  exact hpr.false_of_one_weakSBlock_of_rankTwo h84 h86 hX hH hM4 hthree hL hk1 ho hrank hy

theorem pRank_blockP_le_two {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) (L : Subgroup G) :
    Open.pRank 3 (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ≤ 2 :=
  (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three
    (barM_mono inf_le_left)).trans
    ((hctx.pair.pRank_barM_normalizer_le Nat.prime_three (by decide)).trans hctx.esc.pRank_H.le)

theorem oneImageCentreResidueNotA6_of_cited (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : KFactCentreBlockPLRank) : OneImageCentreResidueNotA6 := by
  intro G _ _ P M A H R hctx hev L hL hk1 hZ h4 hnA6
  have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hfact
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hnot := hctx.pair.nineThree_not_one h85 hX hL
  have hconc := hctx.pair.nineThree h93 hL
  have hsolv := d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair
    hctx.strong hctx.perf L hL
  have h3 := hK G M (pCoreOf 2 H) L hL hconc hnot.1 hnot.2 hsolv (centre_le_blockPL hD2 hctx hL) hZ
    hnA6
  have h2 := pRank_blockP_le_two hctx L
  omega

theorem oneImageCentreResidue_of_notA6 (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hK : KFactBlockCentrePLRank)
    (h : OneImageCentreResidueNotA6) : OneImageCentreResidue := by
  intro G _ _ P M A H R hctx hev L hL hk1 hZ h4
  by_cases he : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
      alternatingGroup (Fin 6))
  · obtain ⟨e⟩ := he
    exact false_of_oneImage_centre_alt_six h93 hD2 hΛ hK hctx hL hk1 hZ e
  · exact h G P M A H R hctx hev L hL hk1 hZ h4 he

theorem oneImageCentreResidue_of_cited (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hK1 : KFactBlockCentrePLRank)
    (hK2 : KFactCentreBlockPLRank) : OneImageCentreResidue :=
  oneImageCentreResidue_of_notA6 h93 hD2 hΛ hK1 (oneImageCentreResidueNotA6_of_cited h93 hD2 hK2)

end CFSG.AGLEmbeddingD2.McLaughlin
