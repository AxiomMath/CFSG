module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpKillType
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.OuterCase

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open CFSG.EvenSporadicStandard CFSG.ComponentClassification.GSThmB

theorem mclStdExclusion_of_container
    (hS : Solomon2AnInput) (hct : McLStd.ContainerIsDoubleCover .McL) : McLStdExclusion :=
  fun _ _ _ _ h => McLStd.mcl_not_standard_of_container hS hct h

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
