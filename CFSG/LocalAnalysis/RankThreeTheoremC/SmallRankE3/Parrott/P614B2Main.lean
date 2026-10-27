module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614B2Hyp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Glue
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSNotDelta

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem pieceCompSylow_holds : PieceCompSylow := by
  intro hKF1 hKF2 G _ _ P M x z H S hyp h0
  obtain ⟨K, hK⟩ := exists_prop614Component hyp.setting hKF1 hKF2 hyp.situation hyp.point
    hyp.central hyp.optimal.ext h0 hyp.core_le
  exact ⟨K, hK.le, hK.normal, hK.not_le, hK.mem, hK.rank_one, hK.perfect, hK.lt, hK.maximal⟩

theorem pieceCompOmega_holds : PieceCompOmega := by
  intro h64 G _ _ P M x z H S hyp hΩ _
  obtain ⟨⟨K, hK⟩, -⟩ := P614B2.kFact64ii_apply h64 hyp hΩ
  exact ⟨K, hK.le, hK.normal, fun hKM => hK.not_le (le_sup_of_le_left (le_inf hKM hK.le)),
    hK.mem, hK.rank_one, hK.perfect, hK.lt, hK.maximal⟩

theorem pieceNotDelta_holds : PieceNotDelta := by
  intro h64 _ _ G _ _ P M x z H S hyp hΩ hnpc
  obtain ⟨-, b, hbB, hbZ, hbN⟩ := P614B2.kFact64ii_apply h64 hyp hΩ
  obtain ⟨g, -, hgconj⟩ := exists_mem_normalizer_conj_zpowers hyp.setting hyp.situation
    hyp.point hyp.central hbB hbZ
  exact hbN (RankFourTheoremC.PEmpty.L6LeavesNS.hasNormalPComplement_inf_centralizer hgconj H hnpc)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
