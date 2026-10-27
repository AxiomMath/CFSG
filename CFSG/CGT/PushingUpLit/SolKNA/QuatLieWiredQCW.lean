module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieCITLift
public import CFSG.ClassicalInvolution.MilestoneAssemblyWired15
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired19

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.MilestoneAssembly
open CFSG.GH74.GLS.Balance (solvableL2PrimeBalance_proved)
open CFSG.ComponentClassification.StandardRecognition (ClassicalInvolutionTheoremModels)

section Inputs

structure CITInputs : Prop where
  gh74 : GH74SectionalModels
  frameLarge : TA3.ResidualCFrameLarge
  twistAllTwin : ∀ n, TightTwistAllTwin n
  largeLiftS : ∀ n, TightLargeLiftS n
  centTwin : ∀ n, TightCentTwinLift n
  r4 : GH74SectionalModels → TightR4

theorem citInputs_of_qcw19 (h : CFSG.ComponentClassification.QuaternionComponent.WiredInputs₁₉)
    (hr4 : GH74SectionalModels → TightR4) : CITInputs where
  gh74 := h.gh74
  frameLarge := h.frameLarge
  twistAllTwin := h.twistAllTwin
  largeLiftS := h.largeLiftS
  centTwin := h.centTwin
  r4 := hr4

end Inputs

section Consequences

theorem CITInputs.toWired15
    (h : CITInputs) : W15.WiredInputs₁₅ where
  gh74 := h.gh74
  tightLift := fun hGH => tightHasMember3LargeBelow_of_leaves₂ tightF1S_holds
    tightEndGameOdd_holds h.twistAllTwin
    (TA3.tightSmallBase_of_twin hGH TA3.twin2M12Leaf_holds TA3.twin2Sz8Leaf_holds
      TA3.twin2AnLeaf_holds) h.largeLiftS h.centTwin (h.r4 hGH)
  smallOddLie := TA3.smallOddLieTightMemberS_holds
  frame := TA3.residualCFrame_of_ranges (TA3.Frame.residualCFrameSmall_of_gh74 h.gh74)
    h.frameLarge

theorem cit3Inductive_of_citInputs
    (h : CITInputs) : CIT3Inductive :=
  (h.toWired15.toWired14 solvableL2PrimeBalance_proved).cit3Inductive

theorem tightLiftSimple_of_citInputs
    (h : CITInputs) : TightLiftSimple :=
  tightLiftSimple_of_leaves₂ (cit3Inductive_of_citInputs h) tightF1S_holds tightEndGameOdd_holds
    h.twistAllTwin
    (TA3.tightSmallBase_of_twin h.gh74 TA3.twin2M12Leaf_holds TA3.twin2Sz8Leaf_holds
      TA3.twin2AnLeaf_holds) h.largeLiftS h.centTwin (h.r4 h.gh74)

theorem classicalInvolutionTheoremModels_of_citInputs
    (h : CITInputs) :
    ClassicalInvolutionTheoremModels :=
  fun G _ _ _ hF z hz J hzJ hJ S hS =>
    h.toWired15.models solvableL2PrimeBalance_proved G hF z hz J hzJ hJ S hS

end Consequences

end CFSG.CGT.PushingUpLit.SolKNA
