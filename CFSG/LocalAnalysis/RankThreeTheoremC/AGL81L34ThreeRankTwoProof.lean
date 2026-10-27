module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenFiveAtOf
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem kFactL34ThreeRankTwo : KFactL34ThreeRankTwo := by
  intro Y _ _ K hK
  obtain ⟨e⟩ := CFSG.AGLEmbedding.KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hK
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  rw [← CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.pRank_congr_of_mulEquiv e,
    CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_projectiveSL hk]

end CFSG.LocalAnalysis.RankThreeTheoremC
