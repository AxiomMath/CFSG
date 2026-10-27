module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section Certs

theorem triPiece_of_innDiag (hIO : InnDiagOrth) (hIE : InnDiagExc) : TriPiece :=
  triPiece_of_pieces hIO hIE CFSG.LocalAnalysis.GLTheoremA.Y10GTri.triOuterD4_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GTri.triFieldTD4_holds

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10GField
