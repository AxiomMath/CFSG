module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionSporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionU35
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionSp44
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionHS

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

theorem onanInspection_holds :
    ONanInspection :=
  onanInspection_of_arms inspectionArm_psu_three_five inspectionArm_psl_three_seven
    inspectionArm_m22 inspectionArm_m23 inspectionArm_m24 inspectionArm_hs inspectionArm_ru
    inspectionArm_psl_five_two inspectionArm_j2 inspectionArm_psp_two_two_two

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
