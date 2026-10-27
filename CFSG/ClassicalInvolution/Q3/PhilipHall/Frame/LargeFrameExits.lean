module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SharedRecog
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Proving.LargeTransport
public import CFSG.ClassicalInvolution.Q3.Q3T7FStar3Frame
public import CFSG.ClassicalInvolution.Q3.TL3F1Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Check

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform

theorem residualCFrameLarge_of_recog_aEmpty (hrec : Q8TwinRecogLarge) (hA : FrameAEmpty)
    (htw : ∀ n, TightTwistAllTwin n) (hsmall : TightSmallBase)
    (hliftS : ∀ n, TightLargeLiftS n) (hliftC : ∀ n, TightCentTwinLift n) :
    TA3.ResidualCFrameLarge := by
  have h11b := tightC19_11bS_of_F1_endgame (IH := fun m => CIT3Below m ∧ TightBelow m)
    tightF1S_holds
    (tightEndGameS_of_solv (tightEndGameSolv_of_odd tightEndGameOdd_holds))
  have hTB : ∀ n, CIT3Below n → TightBelow n := fun n hB =>
    tightInductive_of_step
      (tightStep_of_parts₅ htw hsmall (tightLargeEdgeS_of_core h11b) hliftS hliftC) n hB
  have h := fStarTwinMemberFreeLargeTB_of_recog hrec hA D42.frameExitD42_proved
  exact residualCFrameLarge_of_thm7FStar3Large
    (Proving.fStarTwinSimpleLarge_of_memberFreeLarge
      (fun Y _ _ _ hnab hB Ω K hΩ hK htr hgen htw' hsup hfree h3 hl =>
        h Y hnab hB (hTB _ hB) Ω K hΩ hK htr hgen htw' hsup hfree h3 hl))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
