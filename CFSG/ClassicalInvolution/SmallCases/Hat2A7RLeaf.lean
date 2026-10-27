module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreMain
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NB
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NCore

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.ClassicalInvolution

theorem a7ThmI_of_inductive2A7 (h : Hat2A7.CITInductive2A7) : A7ThmI := by
  intro F _ _ _ hnab K z hw hyp
  obtain ⟨L, hL⟩ := Hat2A7.exists_isClassical2A7_of_witness hyp.orderOf_eq_two hyp.mem
    hyp.subnormal hw
  exact (Hat2A7.false_of_inductive2A7 h hnab hL).elim

theorem a7ThmI_of_coreStep2A7 (h : Hat2A7.CoreStep2A7) : A7ThmI :=
  a7ThmI_of_inductive2A7 (Hat2A7.citInductive2A7_of_coreStep h)

theorem a7ThmI_of_swap_and_B (S : Hat2A7T.TwinSwapExclusion) (B : Hat2A7N.A7BStepN) :
    A7ThmI := by
  have GS : Hat2A7.GoldschmidtStronglyClosedExponent :=
    Hat2A7.goldschmidtStronglyClosedExponent_of_milestone
      @CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian
  have TW : Hat2A7.TwinExclusion :=
    Hat2A7T.twinExclusion_of_core_of_swap GS A7Core.a7FusionCore S
  exact a7ThmI_of_coreStep2A7
    (Hat2A7N.coreStep2A7_of_inputsN GS TW (Hat2A7N.localOddCentralStep2A7N_of_BN B))

end CFSG.ClassicalInvolution.Hat2A7R
