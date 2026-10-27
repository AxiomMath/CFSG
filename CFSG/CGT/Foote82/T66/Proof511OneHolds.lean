module

public import CFSG.CGT.Foote82.T66.Proof511One
public import CFSG.CGT.Foote82.T66.Proof511SylSpor
public import CFSG.CGT.Foote82.T66.Proof511SylJ3
public import CFSG.CGT.Foote82.T66.Proof511SylMcL
public import CFSG.CGT.Foote82.T66.Proof511PSL43
public import CFSG.CGT.Foote82.T66.Proof511Cover
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.CGT.Foote82.T66.Proof511SylLie

public section

namespace CFSG.CGT.Foote82.Proof511

theorem caseILemma511_holds
 :
    CaseILemma511 :=
  caseILemma511_of_inputs
    (fun G _ _ _ hnonab hrank hsect =>
      CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models G hnonab hrank hsect)
    CFSG.SeitzReduction.gls3OddLieAutComponentsInput
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    (fun _ _ _ h P => sqOne_card_M22 h P) (fun _ _ _ h P => sqOne_card_M23 h P)
    (fun _ _ _ h P => sqOne_card_J2 h P) (fun _ _ _ h P => sqOne_card_J3 h P)
    (fun _ _ _ h P => sqOne_card_McL h P)
    (fun _ _ _ _ _ hp hp2 h8 h P => sqOne_card_PSU4 hp hp2 h8 h P)
    (fun _ _ _ _ _ _ hJ hZ hc hc3 hcZ hdim hL => not_psl43 hJ hZ hc hc3 hcZ hdim hL)
    (fun _ _ _ hJ hZ hS => center_eq_bot_of_psp43 hJ hZ hS)

end CFSG.CGT.Foote82.Proof511
