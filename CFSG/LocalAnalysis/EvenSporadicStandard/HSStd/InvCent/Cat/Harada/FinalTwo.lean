module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatLeaf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.CentFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.BenderRows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.E16Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.J1Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.J2Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.L34Row
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.M12Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.PSp45TwoRows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Two

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

section


theorem catHaradaTwoAS_holds : CatHaradaTwoAS :=
  catHaradaTwoAS_of_parts CFSG.ComponentClassification.SolMax.FiveCat.fivePumpLeaf_holds
    catCentFour_holds Harada.noTwoCfgL216_holds Harada.noTwoCfgL34_holds
    Harada.noTwoCfgU34_holds Harada.noTwoCfgL225_holds Harada.noTwoCfgL35_holds
    Harada.noTwoCfgU35_holds Harada.noTwoCfgPSp45_holds Harada.noTwoCfgJ1_holds
    Harada.noTwoCfgJ2_holds Harada.noTwoCfgM12_holds

end

end CFSG.EvenSporadicStandard.HSStd.InvCent
