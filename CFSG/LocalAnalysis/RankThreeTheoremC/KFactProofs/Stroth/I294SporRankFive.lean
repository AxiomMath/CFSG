module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporData
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporB
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporHN
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporLy
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporM5
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporCo1
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporTable

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3


open CFSG.LocalAnalysis.RankFourTheoremC in
theorem sporadicCentralizerRank_holds : SporadicCentralizerRank :=
  sporadicCentralizerRank_of_data sporadicRankTable_holds
    (sporadicClassWitness_of_pairs sporadicClassWitnessAt_Co1_five sporadicClassWitnessAt_HN_five
      sporadicClassWitnessAt_Ly_five sporadicClassWitnessAt_B_five sporadicClassWitnessAt_M_five
      sporadicClassWitnessAt_M_seven)

theorem sporadicCentralizerPPart_of_three (hT : SporadicThreeRankThree)
    (hJ : J3ThreeCentralizer) : SporadicCentralizerPPart :=
  sporadicCentralizerPPart_of_parts sporadicCentralizerRank_holds hT hJ

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
