module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Ctx
public import CFSG.RankThree.PartTwo.Sec21.Item234
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TROne
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Sec
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Twin
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Residues

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.McLaughlin
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem pairOneImageLieTR3_of_gl83 {G : Type} [Group G] [Finite G]
    (hX : D1NoXBlock3 G) (h85 : Asc81bEightFive)
    (hLF : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LargeFieldParabolic)
    (hSA : CFSG.AGLEmbeddingD2.McLaughlin.SmallRankAtlas)
    (hGN : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNilesInput)
    (hCov : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.KFactParabolicCoverOne)
    (hgl : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable) :
    PairOneImageLieTR3 G := by
  intro P M A H R hctx hev L hL hk1 h2 hr hZ
  have hpr := hctx.pair
  have hNX : NoXBlockFor G := noXBlockFor_of_setting hX hctx.setting
  have hsolv : BlockPLThreeSolv M (pCoreOf 2 H) L :=
    blockPLThreeSolv_of_perfectThreePrime hctx.pair hctx.perf hL
  have hSylneg := (hpr.nineThree_not_one h85 hNX hL).2 h2
  have hclass := isClassicalOverTwo_of_nineThreeTwo hLF hSA hL h2 hSylneg hsolv hZ hr
  have hZ' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
    rwa [← card_inf_centralizer_eq_card_center]
  obtain ⟨T, hT2, hQT, hNT, hT⟩ := hctx.exists_twoGroup_of_evenIndex hev
  have hNH := hpr.normalizer_twoCore_H
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hT0 : T ≠ ⊥ := by
    intro h
    apply CFSG.PreuniquenessRankFour.Helpers.twoLocal_pCoreOf_ne_bot hpr.maxTwoLocal_M.1
    exact eq_bot_iff.mpr (hQT.trans h.le)
  have hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L ∨ barM M L' = barM M L := fun L' hL' => Or.inl (hk1 L' hL')
  have hN := normalizes_trJ hL hL hk2 hTM
    (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hSylT := isSylowTwoOf_trX_one hL hT2 hN hQT
    (isSylowTwoOf_barM_inf_of_parabolic hL hT hNH h2)
  have hXM : trX M L L T ≤ M := trX_le hL.le hL.le hTM
  have hTX : T ≤ trX M L L T := le_trX_right
  have hLX : L ≤ trX M L L T := le_trJ_left.trans le_trX_left
  have hD := gnBoundS_of_pair3 hctx hgl hT2 hTX hXM hNT
  have hsec : ¬ ThreeSections L :=
    a6s_not_threeSections_of_block hL.toIsTwoPrimeComponent (by omega) hZ'
  have hmove : ¬ L.subgroupOf (trX M L L T) ≤ gnC (T.subgroupOf (trX M L L T)) := fun hle =>
    a6s_false_of_le_gnC_one hTX hT2 hT0 hD hLX (by omega) hsec hle
  have hGNS := gnSetting_trX hNX hpr.maxTwoLocal_M hpr.isKGroup.1 hpr.charTwo.1 hL hL hT2 hN hTM
    hSylT
  have hC := not_three_dvd_gnC_one hL hk1 hT2 hTH hTM hQT hZ' hmove
  have hcomp := blockStar_isComponent hXM hTX hQT hL hLX hmove
  obtain ⟨-, -, ⟨e⟩, hf⟩ := blockStar_facts hXM hTX hQT hL hLX hmove
  obtain ⟨-, hrk⟩ := hf hZ'
  have hr' : Open.pRank 3 (barM M L) = Open.pRank 3 L :=
    pRank_barM_eq Nat.prime_three (by norm_num) M L hL.le
  have key := isOneImageList_of_gnS hGN hCov hGNS hC hD hcomp
    (IsClassicalOverTwo.of_mulEquiv e hclass) (by omega)
    (blockStar_sylow hXM hTX hL hLX hT2 hSylT)
  exact IsOneImageList.of_mulEquiv e.symm key

end CFSG.LocalAnalysis.RankThreeTheoremC
