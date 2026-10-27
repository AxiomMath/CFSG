module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreTransfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem kd264X1LinPart_holds : KD264X1LinPart :=
  kd264X1LinPart_of_core X1LinCore.Transfer.KD264X1LinCore_holds

theorem kd264X1Row_of_nonLinParts (hSp : KD264X1SpPart) (hOp : KD264X1OmPlusPart) (hOm : KD264X1OmMinusPart)
    (hU : KD264X1UnPart) (hE : KD264X1ExcPart) : KD264X1Row :=
  kd264X1Row_of_parts kd264X1LinPart_holds hSp hOp hOm hU hE

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
