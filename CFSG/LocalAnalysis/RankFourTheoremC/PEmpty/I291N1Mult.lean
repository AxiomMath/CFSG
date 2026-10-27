module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Center

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kdMultP5_of_tables
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSp : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : KDMultP5 :=
  fun _ hp hp5 _ _ _ hq hcat hZ hZp =>
    CFSG.LocalAnalysis.RankFourTheoremC.isLinearOrUnitaryAt_of_tables hGA hSp hp hp5 hq hcat hZ
      hZp

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
