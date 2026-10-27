module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LowRankRow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowCensus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.RankCount
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowClauseO

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData


theorem clauseO_of_pair_rank_le_two (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hU : OutU33)
    (hL5 : OutL5) (hO27 : OutL27) (hK1 : KFactLowRankNineThreeTwo)
    (hK2 : KFactOrthogonalTwoLieRank) {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hw : IsWeakSBlock M (pCoreOf 2 H) L) (hr : Open.pRank 3 L ≤ 2)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    ClauseO M L := by
  have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hfact
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hnot := hctx.pair.nineThree_not_one h85 hX hw
  have hconc := hctx.pair.nineThree h93 hw
  have hsolv := d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair
    hctx.strong hctx.perf L hw
  have hlow : Open.pRank 3 L ≤ 1 → ClauseO M L := fun h1 =>
    clauseO_of_lowRank hO27 hK1 hK2 hw hconc hnot.1 hnot.2 hsolv h1 hZ
  have hrb : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = Open.pRank 3 L := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq Nat.prime_three
      (by norm_num) M L hw.le]
  rcases pairBlockCensus hLF h418 hL27 h93 hD2 G P M A H R hctx L hw with
    h | h | h | h | h | h
  · exfalso
    obtain ⟨-, hc3, -⟩ := h
    apply hZ
    rw [card_inf_centralizer_eq_card_center, hc3]
  · exact clauseO_tightRow hU hL5 hw h.2.2
  · exfalso
    obtain ⟨-, h12⟩ := h
    rcases h12 with h12 | h12
    · obtain ⟨e⟩ := h12
      have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
        hrb
      have := le_pRank_alternatingGroup_three (N := 12) (k := 3) (by norm_num)
      omega
    · obtain ⟨e⟩ := h12
      have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
        hrb
      have := le_pRank_alternatingGroup_three (N := 16) (k := 3) (by norm_num)
      omega
  · exact hlow h
  · exfalso
    obtain ⟨-, hr3⟩ := h
    omega
  · exact absurd h.1 hZ

theorem twoImageLowRankKill_of_cited (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hU : OutU33) (hL5 : OutL5) (hO27 : OutL27)
    (hK1 : KFactLowRankNineThreeTwo) (hK2 : KFactOrthogonalTwoLieRank) :
    ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
      PairStrongCtx P M A H R →
      ∀ L₁ L₂ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ → IsWeakSBlock M (pCoreOf 2 H) L₂ →
      barM M L₁ ≠ barM M L₂ →
      (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
        barM M L' = barM M L₁ ∨ barM M L' = barM M L₂) →
      (¬ 3 ∣ Nat.card (barM M L₁ ⊓
        Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) →
      (¬ 3 ∣ Nat.card (barM M L₂ ⊓
        Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) →
      Open.pRank 3 L₁ ≤ 1 → Open.pRank 3 L₂ ≤ 2 → False := by
  intro G _ _ P M A H R hctx L₁ L₂ hL₁ hL₂ hne hk2 hZ₁ hZ₂ hr₁ hr₂
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
  have hc₁ := clauseO_of_pair_rank_le_two hLF h418 hL27 h93 hD2 hU hL5 hO27 hK1 hK2 hctx hL₁
    (by omega) hZ₁
  have hc₂ := clauseO_of_pair_rank_le_two hLF h418 hL27 h93 hD2 hU hL5 hO27 hK1 hK2 hctx hL₂
    hr₂ hZ₂
  have hcount := rank_count_two_weakSBlocks hpr h84 h86 hX hH hM4 hthree hL₁ hL₂ hne hk2
    (fun L hL u hu hp => by
      rcases hL with rfl | hL
      · exact hc₁ u hu hp
      · rw [Set.mem_singleton_iff] at hL
        subst hL
        exact hc₂ u hu hp)
    (fun L hL => by
      rcases hL with rfl | hL
      · exact hZ₁
      · rw [Set.mem_singleton_iff] at hL
        subst hL
        exact hZ₂)
  omega

end CFSG.AGLEmbeddingD2.McLaughlin
