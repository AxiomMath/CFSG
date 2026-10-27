module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatLeaf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.BenderRows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.J1Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.J2Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.M12Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.PSp45Rows

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

section


theorem catHaradaAS_holds : CatHaradaAS :=
  catHaradaAS_of_parts CFSG.ComponentClassification.SolMax.FiveCat.fivePumpLeaf_holds
    Harada.noZ2S5L216_holds Harada.noZ2S5U34_holds Harada.noZ2S5PSp45_holds
    Harada.noZ2S5J1_holds Harada.noZ2S5J2_holds Harada.haradaM12_holds

end

end CFSG.EvenSporadicStandard.HSStd.InvCent
