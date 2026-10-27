module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofR
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofTorusSL
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofTorusSU

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

theorem gl83PElementCentralizerRank_of_tables (hGA : CFSG.Open.GriessAllModelsStatement) :
    GL83PElementCentralizerRank :=
  gl83PElementCentralizerRank_of_tori hGA
    (fun {_ _ _} _ _ hp hn hpK s hs => l212in_torusHom_sl hp hn hpK s hs)
    (fun {_ _ _ _} _ {_} _ _ _ hp hn hK hpq s hs => l212in_torusHom_su hp hn hK hpq s hs)

end CFSG.LocalAnalysis.RankFourTheoremC
