module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFFinal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertF
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6STriProof
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Asm56
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf63E64Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22DShapesE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Asm52
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SAE8Proof
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertBAE8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertC2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3


theorem twinPerpV3E_of_triFin
    (hTF : TwinPerpV3.A6S.AE6TriFin) (n : ℕ) (hA : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) : TwinPerp.TwinPerpV3E n := by
  have hLEnd : CFSG.ClassicalInvolution.Q3.TC.Thin.DLeafEnd 3
      (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3) :=
    CFSG.ClassicalInvolution.Q3.Sec13.dLeafEnd_three _
  haveI : TwinThmEW.PrintedQuotOdd := TwinThmEW.printedQuotOdd_proved
  haveI : TwinThmEW.PrintedQuotCent := TwinThmEW.printedQuotCent_proved
  haveI : TwinThmEW.PrintedHull := TwinThmEW.printedHull_proved
  have hWF : TwinThmEW.WFreeToAll := TwinThmEW.wFreeToAll_proved
  have hEQ : TwinThmEW.ThmEQ8 := TwinThmEW.thmEQ8_of_dLeafEnd hLEnd
  have hC : TwinPerpV3.A6S.V3AE6EComm n :=
    TwinPerpV3.A6c.v3AE6EComm_of TwinPerpV3.A6b.v3AE6E_proved
  have hDN : TwinPerpV3.A6S.V3AE6DNorm n := TwinPerpV3.A6DN.v3AE6DNorm_proved hC
  have hI : TwinPerpV3.A6S.V3AE6I n :=
    TwinPerpV3.A6d.v3AE6I_of_c hP (TwinPerpV3.A6S.v3AE6D_of TwinPerpV3.A6b.v3AE6E_proved hC) hDN
  exact TwinPerpV3.twinPerpV3E_of_steps42ON hEQ (TwinThmEW.twinThmEP_of_thmEQ8W hEQ hWF n) hA hP
    (TwinThmEW.t4Supply_of_twoClass n hA hP) TwinCentRes.modelFactSp62
    TwinCentRes.modelFactD42_of_cert TwinCentRes.modelFactM12_of_certs
    (TwinPerpV3.secEdgelessConcl163_proved hA hP) (TwinPerpV3.secTwinNoRoot_of hA hP)
    (TwinPerpV3.GX.v3LayerGenExConjAd_proved n hA hP)
    (TwinPerpV3.v3SecOpenW_of_models hA hP (TwinThmEW.t4Supply_of_twoClass n hA hP)
      TwinDisc.e4Sp6SqModel_of_certs TwinDisc.e4O8TwinModel_of_certs TwinDisc.E64.e64AutModel_of_cert)
    (TwinPerpV3.A6Asm.v3ExitAE6WfN_of_parts52 hEQ (TwinThmEW.twinThmEP_of_thmEQ8W hEQ hWF n) hA hP
      (TwinThmEW.t4Supply_of_twoClass n hA hP) TwinCentRes.modelFactSp62
      TwinCentRes.modelFactD42_of_cert TwinCentRes.modelFactM12_of_certs
      (TwinPerpV3.secEdgelessConcl163_proved hA hP) (TwinPerpV3.secTwinNoRoot_of hA hP)
      (TwinPerpV3.GX.v3LayerGenExConjAd_proved n hA hP)
      (TwinPerpV3.v3SecOpenW_of_models hA hP (TwinThmEW.t4Supply_of_twoClass n hA hP)
        TwinDisc.e4Sp6SqModel_of_certs TwinDisc.e4O8TwinModel_of_certs TwinDisc.E64.e64AutModel_of_cert)
      A6h1.ae6ModelPar_proved (TwinPerpV3.A6Asm.v3AE6I23_proved hP)
      (TwinPerpV3.A6h2.v3AE6Glue_of_cert hI
        (TwinPerpV3.A6S.ae6ModelAE8_of_fin TwinPerpV3.A6S.ae6AE8Fin_proved)
        TwinPerpV3.A6S.ae6EdgePairsFin_proved (TwinPerpV3.A6S.ae6ModelTri_of_fin hTF))
      TwinPerpV3.A6S.ae6FFin_proved TwinPerpV3.A6S.ae6C2Search_proved)
    (TwinPerpV3.WF.v3WFinalWg_proved n hA hP)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
