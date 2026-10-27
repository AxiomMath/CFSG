module

public import CFSG.CGT.Timmesfeld75.Final
public import CFSG.CGT.Timmesfeld75.BenderInputs2
public import CFSG.CGT.Timmesfeld75.BenderInputs3
public import CFSG.CGT.Timmesfeld75.BenderInputs4

public section

namespace CFSG.CGT.Timmesfeld75

structure ReducedLiteratureInputs : Prop where
  aschbacherNoPolar : AschbacherNoPolarInput
  aschbacherTheoremOne : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne
  benderCenter : BenderCenterInput
  unitaryTwoGeneration : UnitaryTwoGenerationInput

theorem LiteratureInputs.of_reduced
    (L : ReducedLiteratureInputs) : LiteratureInputs where
  aschbacherNoPolar := L.aschbacherNoPolar
  aschbacherTheoremOne := L.aschbacherTheoremOne
  benderCenter := L.benderCenter
  unitaryTwoGeneration := L.unitaryTwoGeneration
  benderSimple := benderSimpleInput_of_repo
  benderList := benderListInput_of_repo
  benderTransitive := benderTransitiveInput_of_repo

theorem theoremA_of_reduced_inputs
    (L : ReducedLiteratureInputs) (P : PaperStepInputs) :
    TheoremAStmt :=
  theoremA_of_inputs (LiteratureInputs.of_reduced L) P

theorem node_of_reduced_inputs
    (L : ReducedLiteratureInputs) (P : PaperStepInputs) :
    NodeStatement :=
  node_of_inputs (LiteratureInputs.of_reduced L) P

end CFSG.CGT.Timmesfeld75
