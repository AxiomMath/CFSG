module

public import CFSG.CGT.Timmesfeld75.FinalReduced5
public import CFSG.CGT.Timmesfeld75.Sec5Eleven
public import CFSG.CGT.Timmesfeld75.FinalReduced4

public section

namespace CFSG.CGT.Timmesfeld75

structure Step511Inputs : Prop where
  listWC : ListWCIdentification
  a9 : A9Input
  altCover : AltCoverInput
  mult : MultPrimeInput
  small64 : Small64Input
  lemma29 : Lemma29Input

structure RefinedStepInputs2 : Prop where
  a1 : StepA1Inputs
  s511 : Step511Inputs
  step69 : Step69
  step68 : Step68
  step610 : Step610
  step79 : Step79
  step711 : Step711
  step81 : Step81
  step82 : Step82

theorem RefinedStepInputs2.toCore
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hD : Section3DihedralInput) (P : RefinedStepInputs2) : CoreStepInputs where
  stepA1 := stepA1_of (lemma214_of_remaining L) involutionClassInput_of_repo
    (section3IsoInput_of_remaining L hSz hD) L.aschbacherTheoremOne benderWCInput_of_repo
    P.a1.noA P.a1.nine P.a1.stepOne P.a1.corB P.a1.shult P.a1.yCase
  step511 := step511_core_of (lemma214_of_remaining L) involutionClassInput_of_repo
    (section3IsoInput_of_remaining L hSz hD)
    (lemma215_of_literature (LiteratureInputs.of_reduced (ReducedLiteratureInputs.of_remaining L)))
    P.s511.listWC P.s511.a9 P.s511.altCover P.s511.mult P.s511.small64 P.s511.lemma29
    P.a1.noA P.a1.nine
    (step57_of_stepA1 (lemma214_of_remaining L) involutionClassInput_of_repo
      L.aschbacherTheoremOne benderWCInput_of_repo
      (stepA1_of (lemma214_of_remaining L) involutionClassInput_of_repo
        (section3IsoInput_of_remaining L hSz hD) L.aschbacherTheoremOne benderWCInput_of_repo
        P.a1.noA P.a1.nine P.a1.stepOne P.a1.corB P.a1.shult P.a1.yCase))
  step69 := P.step69
  step68 := P.step68
  step610 := P.step610
  step79 := P.step79
  step711 := P.step711
  step81 := P.step81
  step82 := P.step82

theorem theoremA_of_refined2
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hD : Section3DihedralInput) (P : RefinedStepInputs2) : TheoremAStmt :=
  theoremA_of_parts L hSz hD (P.toCore L hSz hD)

theorem node_of_refined2
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hD : Section3DihedralInput) (P : RefinedStepInputs2) : NodeStatement :=
  node_of_parts L hSz hD (P.toCore L hSz hD)

end CFSG.CGT.Timmesfeld75
