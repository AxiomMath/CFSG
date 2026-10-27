module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterNPCMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterSylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section Certified


theorem kFact64iiOuterNPC_holds : KFact64iiOuterNPC :=
  kFact64iiOuterNPC_of_outerSylow kFact64iiOuterSylow_holds

end Certified

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
