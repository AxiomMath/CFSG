module

public import CFSG.LocalAnalysis.EvenBN.U5.LinGlue
public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin3102
public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin39d
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43Two
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43Out
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightB
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineReduced
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofElevenTrans
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerListK

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open CFSG.LocalAnalysis.EvenBN

theorem u5LinearCaseExclusion_holds :

    CFSG.Yardstones.M41b0c98b3153.U5LinearCaseExclusion :=
  u5LinearCaseExclusion_of_steps GMSK.gmsUnitarySharpKRankOne
    GMSK.gmsLinearStandardLayerListKRankOne
    { s38b := fun _ _ _ _ _ _ _ _ hp ha => Data.sec38_input hp ha
      s39d := fun _ _ _ _ _ _ _ _ hl k8 S hS hP ha hb hc => Data.lin_sec39d hl k8 S hS hP ha hb hc
      s39r := fun _ _ _ _ _ _ _ _ hp k he hi hnn ho => Data.sec39_reduced hp k he hi hnn ho
      s310c := fun _ _ _ _ _ _ _ _ hl k hO => Data.lin_sec3102 hl k hO
      s311a := fun _ _ _ _ _ _ _ _ hp k => Data.sec311Trans_of_hyp hp k
      a4 := fun _ _ _ _ _ _ _ _ hl k c h41 h42 h43 =>
        Data.CaseBData.lin_sec43_two hl k c h41 h42 h43
      a6 := fun _ _ _ _ _ _ _ _ hl k c R hR hSR => Data.CaseBData.lin_sec43_out hl k c R hR hSR }

end CFSG.LocalAnalysis.EvenBN.U5
