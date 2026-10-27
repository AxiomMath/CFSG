module

public import CFSG.CGT.Timmesfeld75.FinalReduced2
public import CFSG.CGT.Timmesfeld75.Step511Card

public section

namespace CFSG.CGT.Timmesfeld75

structure CoreStepInputs : Prop where
  stepA1 : StepA1
  step511 : Step511Core
  step69 : Step69
  step68 : Step68
  step610 : Step610
  step79 : Step79
  step711 : Step711
  step81 : Step81
  step82 : Step82

theorem PaperStepInputs.of_core
    (L : ReducedLiteratureInputs) (hIso : Section3IsoInput)
    (P : CoreStepInputs) : PaperStepInputs :=
  PaperStepInputs.of_reduced L
    { stepA1 := P.stepA1
      step511 := step511_of_core (lemma214_of_literature (LiteratureInputs.of_reduced L))
        involutionClassInput_of_repo hIso P.step511
      step69 := P.step69
      step68 := P.step68
      step610 := P.step610
      step79 := P.step79
      step711 := P.step711
      step81 := P.step81
      step82 := P.step82 }

theorem theoremA_of_core_steps
    (L : ReducedLiteratureInputs) (hIso : Section3IsoInput)
    (P : CoreStepInputs) : TheoremAStmt :=
  theoremA_of_reduced_inputs L (PaperStepInputs.of_core L hIso P)

theorem node_of_core_steps
    (L : ReducedLiteratureInputs) (hIso : Section3IsoInput)
    (P : CoreStepInputs) : NodeStatement :=
  node_of_reduced_inputs L (PaperStepInputs.of_core L hIso P)

end CFSG.CGT.Timmesfeld75
