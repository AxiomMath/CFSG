module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnOut
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Wire
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf15Supply

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

set_option linter.unusedSectionVars false

theorem twinConnPreludeOut_proved :
    ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → TwinConnPreludeOut n :=
  fun n hA hP => preludeOut_of_V₃ TwinCentRes.modelFactSp62 TwinCentRes.modelFactD42_of_cert
    TwinCentRes.modelFactM12_of_certs
    (TwinExitPf10.twinConnInputsV₃_of_thm4 (TwinThmEW.t4Supply_of_twoClass n hA hP))

theorem twinConnEdgesOut_proved :
    ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → TwinConnEdgesOut n :=
  fun n hA hP => edgesOut_of_V₃ TwinCentRes.modelFactSp62 TwinCentRes.modelFactD42_of_cert
    (TwinExitPf10.twinConnInputsV₃_of_thm4 (TwinThmEW.t4Supply_of_twoClass n hA hP))

theorem twinE4Perfect_proved :
    ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → TwinE4Perfect n :=
  fun n hA hP => twinE4Perfect_of_certsOut TwinCentRes.modelFactSp62
    TwinCentRes.modelFactD42_of_cert TwinCentRes.modelFactM12_of_certs
    (twinConnPreludeOut_proved n hA hP) (twinConnEdgesOut_proved n hA hP)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
