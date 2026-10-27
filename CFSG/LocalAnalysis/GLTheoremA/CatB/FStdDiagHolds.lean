module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagRed
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagLin
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagUni
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagExcHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

section Holds


theorem smallCentreS_holds : SmallCentreS :=
  smallCentreS_of_res smallFam_lin smallFam_uni smallFam_symp smallFam_orth smallExcRes_holds

theorem stdCovDiagCentreAt_holds : StdCovDiagCentreAt :=
  stdCovDiagCentreAt_of_S smallCentreS_holds

theorem stdCovDiagOddAt_holds :
    StdCovDiagOddAt :=
  stdCovDiagOddAt_of_S smallCentreS_holds

end Holds

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
