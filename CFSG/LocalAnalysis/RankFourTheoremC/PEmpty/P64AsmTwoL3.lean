module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwo
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64L3GenCore
public import CFSG.LocalAnalysis.GL83PartI.I713.Final

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section RankTwo


theorem kFactP65RankTwo_of_kdata' (hChevP : KDI278ChevP) (hChevQ : KDI278ChevQ)
    (hSpor : KDI278Spor) (hSporB : KDI278SporB) (hSporC : KDI278SporC) (hI204 : KDL64I204U3) :
    KFactP65RankTwo :=
  kFactP65RankTwo_of_kdata GL83.I713.i_7_13_1_holds hChevP kdi278L3_holds hChevQ hSpor hSporB
    hSporC hI204

end RankTwo

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
