module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Assembly
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23.Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwinFactsOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S8Close
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Rows
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf51CaseITF
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIIFStarPf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.SocFactsL33
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.SocFactsM12
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.SocFactsOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.SocFactsU33

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A


theorem thm3RStepG_of_open_parts (h3 : ∀ m, Thm3RTwoOrbit m) (h4 : ∀ m, Thm3RThmB m)
    (h5 : ∀ m, Thm3RO2Lift m) (h7 : ∀ m, Thm3RTwoClass m) (h7' : ∀ m, Thm3RTwoClassG23 m)
    (h8 : ∀ m, Thm3RStdSimple m) (h9 : ∀ m, Thm3RStdOuter m) : ∀ m, Thm3RStepG m :=
  thm3RStepG_of_parts thm3RLiftSub_proved h3 h4 h5 thm3RFStar_proved h7 h7' h8 h9

theorem thm3RStepG_of_remaining
    (hTQ : S7Ident.TwinQ8Class) : ∀ m, Thm3RStepG m :=
  thm3RStepG_of_open_parts S3.thm3RTwoOrbit_proved ThmB.thm3RThmB_proved S5.thm3RO2Lift_proved
    (S7.thm3RTwoClass_of_facts S7Ident.socleOddCore_proved S7Ident.twinOddCore_proved
      S7Ident.l33Q8Class_proved
      S7Ident.u33Q8Classes_proved S7Ident.m12Q8Classes_proved hTQ S7Cert.inspectionFacts_proved
      S7Cert.rowClassAEmpty_proved) S7G23.thm3RTwoClassG23_proved
    thm3RStdSimple_proved
    (Frame.FStar.thm3RStdOuter_of_cases Frame.FrameAEmptyPf.frameCaseITF_proved
      Frame.FrameAEmptyPf.frameCaseIITF_proved)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
