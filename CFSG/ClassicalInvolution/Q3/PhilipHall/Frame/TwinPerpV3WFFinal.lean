module

public import CFSG.ClassicalInvolution.Q3.Sec13EndFinal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22SecELd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22SecNR4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3GXMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFFacts
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22CMerge
public import CFSG.Quasithin.H13.L32NSp4Over

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3

theorem v3WFinalWg_proved
    (n : ℕ) (hA : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) :
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.V3WFinalWg n := by
  have hLEnd : CFSG.ClassicalInvolution.Q3.TC.Thin.DLeafEnd 3
      (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3) :=
    CFSG.ClassicalInvolution.Q3.Sec13.dLeafEnd_three _
  have hEQ : TwinThmEW.ThmEQ8 := TwinThmEW.thmEQ8_of_dLeafEnd hLEnd
  have h4 : Thm4RTwinBelow 3 n := TwinThmEW.t4Supply_of_twoClass n hA hP
  have hSec := TwinPerpV3.secEdgelessConcl163_proved hA hP
  have hSec4 := TwinPerpV3.secTwinNoRoot_of hA hP
  have hGenExC := TwinPerpV3.GX.v3LayerGenExConjAd_proved n hA hP
  have hAb' := v3AbelianO2_of_tr h4 (v3AbelianO2Tr_of_split (v3AbelianO2TrS3_of_edgeless hSec)
    (v3AbelianO2TrG4_of_noRoot' hP hA hSec4))
  have hU3 := v3Hyp51U3E8_of_abelianO2 hAb'
  have h51 := v3Hyp51U_of_model TwinCentRes.modelFactSp62 TwinCentRes.modelFactD42_of_cert
    TwinCentRes.modelFactM12_of_certs h4 hU3
  have hB := v3Hyp51B_of_vertices h51
  have hStarF := v3Hyp51StarF_of_model TwinCentRes.modelFactSp62 TwinCentRes.modelFactD42_of_cert
    TwinCentRes.modelFactM12_of_certs h4
  have hαF := v3FourthAlphaF_of_star hB hStarF
  have h5 := v3Fourth_of_alphaF hαF
  have h7 := v3Alpha1_of_partsWAllC hEQ hA hP h4 hB h5 hαF hStarF
    (v3LayerGenAllC_of_exitConj hA hP h4 hGenExC)
  exact v3WFinalWg_of_facts hEQ hA hP h4 h5 h7

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
