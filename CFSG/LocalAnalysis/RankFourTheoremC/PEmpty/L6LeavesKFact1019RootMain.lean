module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019RootOrth
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019RootUnit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019RootExc

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

section Certified


theorem kFact1019_holds : KFact1019 :=
  kFact1019_of_involutionAt involution_typeA4 involution_typeTwistedA4 involution_typeB3
    involution_typeC3 involution_typeD4 involution_typeTwistedD4 involution_typeE6
    involution_typeTwistedE6 involution_typeE7 involution_typeE8 involution_typeF4
    involution_typeTrialityD4

end Certified

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
