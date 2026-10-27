module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R6AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Str
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7AE6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Out
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7ZC

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section E7AE

variable {n : ℕ}

theorem p23E7Y_of_out_steps' (hAE : P23E6AE' n) (h6 : P23E7AE6 n) (hZC : P23E7ZC n)
    (hEl : P23E7Elem n) (hSt : P23E7Strong n) (hO : GoldOutCyc) : P23E7Y n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hY hE
  rcases hY with hZ | hA5
  · have hZ' := hZC Y R S t K' W u e g hc hno hE hZ
    obtain ⟨T, A, hAC, hAT, hueA, hA2, hAB, hcl⟩ := hSt hcit hP Y R S t K' W u e g hc hno hE hZ'
    have hcomm := comm_of_mem_p23ABar (hEl hcit hP Y R S t K' W u e g hc hno hE hZ') hAC hA2 hAB
    exact p23_178_of_out hO hc T hAT ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩ hcl hueA
  · exact h6 Y R S t K' W u e g hc hno hE (hAE hcit hP Y R S t K' W u e g hc hA5)

theorem p23E7Y_of_fus' (hT : Thm4RTwinBelow 3 n)
    (hT4 : TwinThmE.T4Supply) (hmodel : TwinDisc.ExitE4.E4ModelDStar)
    (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n) (hOrb : P23E7Orb n) (hF : P23E7Fus n)
    (hO : GoldOutCyc) : P23E7Y n :=
  p23E7Y_of_out_steps' (p23E6AE'_proved hT4 hmodel hD4 hMu) p23E7AE6_proved (p23E7ZC_of_thm4 hT)
    (p23E7Elem_of_orb hOrb) (p23E7Strong_of_steps hF hOrb) hO

end E7AE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
