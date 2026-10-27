module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IKFact
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IA5
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem piece620iii_of_kFactCampbellBlock (hBlock : KFactCampbellBlock) : Piece620iii := by
  intro _hCamp h2813 h283 G _ _ hOF hCT P M x z H S K b hyp h618 _h619 h620
  rcases h620.kbar with ⟨-, hA⟩ | hL
  · exact P614I.stage620iii_of_a5Case h283 hyp h618 hA
  · exact P614I.stage620iii_of_kbarL32 hBlock h2813 hOF hCT hyp h618 h620 hL

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
