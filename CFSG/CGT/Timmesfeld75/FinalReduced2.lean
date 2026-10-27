module

public import CFSG.CGT.Timmesfeld75.FinalReduced
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.CGT.Timmesfeld75.BenderInputs5
public import CFSG.CGT.Timmesfeld75.BenderInputs6

public section

namespace CFSG.CGT.Timmesfeld75

structure ReducedStepInputs : Prop where
  stepA1 : StepA1
  step511 : Step511
  step69 : Step69
  step68 : Step68
  step610 : Step610
  step79 : Step79
  step711 : Step711
  step81 : Step81
  step82 : Step82

theorem PaperStepInputs.of_reduced
    (L : ReducedLiteratureInputs) (P : ReducedStepInputs) :
    PaperStepInputs where
  step57 := step57_of_stepA1 (lemma214_of_literature (LiteratureInputs.of_reduced L))
    involutionClassInput_of_repo L.aschbacherTheoremOne benderWCInput_of_repo P.stepA1
  step511 := P.step511
  step69 := P.step69
  step68 := P.step68
  step610 := P.step610
  step79 := P.step79
  step711 := P.step711
  step81 := P.step81
  step82 := P.step82

end CFSG.CGT.Timmesfeld75
