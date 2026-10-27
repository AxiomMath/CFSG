module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Main
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.OpenTen
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureFinal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

theorem pNonemptyConfinement_of_componentPCoreTrivial
    (h10 : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial) :
    CFSG.Yardstones.Md8ed6d263d89.YSPNonemptyConfinement :=
  pNonemptyConfinement_of_kfacts h10
    (CFSG.LocalAnalysis.RankFourTheoremC.gl83NongenerationList_of_componentPCoreTrivial h10)
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds

end CFSG.LocalAnalysis.RankFourTheoremC.P5
