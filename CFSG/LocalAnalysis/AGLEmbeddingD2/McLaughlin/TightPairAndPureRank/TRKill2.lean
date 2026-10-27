module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRA8
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeKill
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.RankImage
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Target

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem rankImageOne_proved : RankImageOne := fun f N h =>
  OrdinaryProofs.pRank_map_le_one Nat.prime_three (by norm_num) f h

theorem pairNineThreeThreeA8Kill_of_two (h : KFactNineThreeThreeTwo) :
    PairNineThreeThreeA8Kill := by
  intro G _ _ M S L hK hA hw hX hS h3 hZ ⟨e8⟩ hsolv
  refine h G M S L hK hA hw hX hS h3 ?_ ?_ hsolv
  · rw [← pRank_top_quot_center_eq hw.le hZ]
    exact le_pRank_of_mulEquiv_alternatingGroup (k := 2) (n := 8) e8 (by norm_num)
  · rintro ⟨e6⟩
    obtain ⟨e6'⟩ := quotCenterEquivAlt (by norm_num : 5 ≤ 6) e6
    have := Nat.card_congr (e6'.symm.trans e8).toEquiv
    rw [card_alt_fin (by norm_num), card_alt_fin (by norm_num)] at this
    norm_num [Nat.factorial] at this

end CFSG.AGLEmbeddingD2.McLaughlin
