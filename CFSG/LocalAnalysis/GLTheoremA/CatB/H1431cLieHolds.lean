module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieAsm
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOrdMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieThreeMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieInnMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutAll
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

section Holds


theorem i1431LieS_holds : I1431LieS :=
  i1431LieS_of_residuals lieSTypeChar_holds lieS3_holds lieSInn_holds lieSOut_holds lieSTwo_holds
    lieSEight_holds

end Holds

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
