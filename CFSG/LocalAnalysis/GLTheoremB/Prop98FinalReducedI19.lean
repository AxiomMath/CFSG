module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma911FinalCertified
public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof
public import CFSG.LocalAnalysis.GL83PartI.I_22_5
public import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof
public import CFSG.LocalAnalysis.GLTheoremB.Input27_9_3Proof
public import CFSG.LocalAnalysis.GLTheoremB.Input20_1Proof
public import CFSG.LocalAnalysis.GLTheoremB.Input19_1_6Proof

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open


theorem prop98_final_reduced'''' (i11 : Input11_6) (i19 : Input19Delta) (h95 : Prop95)
    (i113 : Input11_3) (i279 : Input27_9_3Transv) (hOrth : InputPiGenOrth) : Prop98 :=
  prop98_final_certified input20_1_proved i11 lemma23_proved i19 input19_1_6_proved h95 i113
      (input27_9_3_of_transv i279) GL83.I_22_5_proved (inputPiGen_of_orth hOrth)

end CFSG.LocalAnalysis.GLTheoremB
