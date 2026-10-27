module

public import CFSG.ClassicalInvolution.Q3.Q3DInputs7
public import CFSG.ClassicalInvolution.Q3.Q3JIDisc
public import CFSG.ClassicalInvolution.Q3.Q3AMTriFinal
public import CFSG.ClassicalInvolution.Q3.Q3T8P26Top
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenProved
public import CFSG.ClassicalInvolution.Q3.Q3T6XWire
public import CFSG.ClassicalInvolution.Q3.Q3T6XWire2
public import CFSG.ClassicalInvolution.Q3.Q3T6YFinal
public import CFSG.ClassicalInvolution.Q3.Q3TWBMain
public import CFSG.ClassicalInvolution.Q3.Q3TWBR02
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22RowsU
public import CFSG.ClassicalInvolution.Q3.Q3T7W21P07
public import CFSG.ClassicalInvolution.Q3.Q3OCLChain22
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Fin2
public import CFSG.ClassicalInvolution.Q3.Q3T7S23D05
public import CFSG.ClassicalInvolution.Q3.Q3OCLE04
public import CFSG.ClassicalInvolution.Q3.Q3OCLY02
public import CFSG.ClassicalInvolution.Q3.Q3T7Assembly

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.JI

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Disc3


theorem smallDisconnected3J_proved (hIH : Asc77.IHInterface8 3) (hqs : Q3.QuasisimpleConnected3) :
    SmallDisconnected3J := by
  have hmin : Q3T6X.Fusion3MinBranch := Q3T6X.fusion3MinBranch_of_all Q3T6Y.fusion3MinAll
  have hΩ : HypOmegaModDU 3 1 := Q3T6X.hypOmegaModDU_three_of_fusionMin hmin
  have hA : AEmptyDU 3 1 := Q3T6X.aEmptyDU_three_of_fusionMin hmin
  have hs : AscStand3OfBranch := ascStand3OfBranch_of hΩ hA ih8T_three_proved
  have hE := Q3T8.Asc77.thmE3_of_qs3 hqs
  have hTE : TwoElementsNormalizeU (.sl2 3 1) :=
    Q3T6X.twoElementsNormalizeU_three_of_min Q3T6Y.fusion3MinAll
  have hOCFI : Q3AM.OddCoreFreeA2DiscD3I :=
    Q3AM.oddCoreFreeA2DiscD3I_of_thm5Bad3I hTE ih8T_three_proved hIH Q3AM.thm5Bad3I_proved
      (Q3TWB.twinBridge3_of_inputs hTE ih8T_three_proved Q3T7.twinFrameHyp51uC_proved)
  have h21 : Q3T7.C21_2Three :=
    Q3T7W21.c21_2Three_proved hE Q3T8.Asc77.twinFrameHyp51t_proved
      (Q3T8.Asc77.twinFrameHyp51u_of_rows3 Q3T7.twinOuterAlphaAll3_proved)
  have h22 : Q3T7.C22_1Three := Q3OCL.c22_1Three_of_rows_noEx hE Q3T7.twinSqAlphaAll3_proved
  have h233 : Q3T7.C23_3Three := Q3T7S23.c23_3Three_of_residuals hE
    (Q3T7S23.phan23Residual3_of_oddCore (Q3OCL.oddCoreLayer23Neg3_of_thmE hE)
      Q3OCL.oddCoreLayer23Sp3_proved
      Q3OCL.oddCoreLayer23Plus3_proved)
  have h7 : Thm7A3 :=
    Q3T7.thm7A3_of_residuals ⟨h21, h22, h233, hqs, Q3T7P24.hyp51TwinInnerThree_proved⟩
  exact smallDisconnected3J_of_oddCoreFreeA2DiscD3I hOCFI hs Q3T6.thm6A3_proved h7
    Q3T8.Asc77.thm8A3_proved

end CFSG.ClassicalInvolution.Q3.JI
