module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegCoreMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.LocalAnalysis.GLTheoremA.Y10GField


theorem i14NegFactS_of_innDiagExc (hInn : InnDiagExc) : I14NegFactS :=
  Y10GNeg.i14NegFactS_of_core Y10GNegCore.U6Core_holds i14NegPieceB_holds i14NegPieceC_holds
    (i14NegPieceD_of_innDiagExc hInn)

end CFSG.LocalAnalysis.GLTheoremA.Y10F
