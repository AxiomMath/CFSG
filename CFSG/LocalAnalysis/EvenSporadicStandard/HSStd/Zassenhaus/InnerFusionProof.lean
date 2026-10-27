module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFusionHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerSylow

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem hsInnerFusion : HSInnerFusion :=
  hsInnerFusion_of_innerData_hs fun _ _ _ _ _ _ hL hS hSL hz hz2 hcent =>
    innerData_of_sylow hL hS hSL hz hz2 hcent

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
