module

public import CFSG.CGT.Timmesfeld75.FinalReduced9
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIMain

public section

namespace CFSG.CGT.Timmesfeld75

structure StepA1Inputs3 : Prop where
  caseI : Sec4CaseI
  caseIIIEight : Sec4CaseIIIEight
  nine : Sec4Nine
  stepOne : Sec56StepOne
  corB : Sec56CorB
  shult : Sec57Shult
  yCase : Sec57Y

structure RefinedStepInputs6 : Prop where
  a1 : StepA1Inputs3
  s511 : Step511Inputs
  step69 : Step69
  corB68 : Sec68CorB
  step610 : Step610
  s6 : Sec6Inputs2
  s7 : Sec7Inputs
  lemma26 : Lemma26Input
  step81 : Step81
  step82 : Step82

theorem RefinedStepInputs6.toRefined5
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (P : RefinedStepInputs6) : RefinedStepInputs5 where
  a1 :=
    { caseI := P.a1.caseI
      caseIII := sec4CaseIII_of_inputs (lemma214_of_remaining L) involutionClassInput_of_repo hSz
        L.aschbacherTheoremOne benderWCInput_of_repo P.a1.caseIIIEight
      nine := P.a1.nine
      stepOne := P.a1.stepOne
      corB := P.a1.corB
      shult := P.a1.shult
      yCase := P.a1.yCase }
  s511 := P.s511
  step69 := P.step69
  corB68 := P.corB68
  step610 := P.step610
  s6 := P.s6
  s7 := P.s7
  lemma26 := P.lemma26
  step81 := P.step81
  step82 := P.step82

theorem theoremA_of_refined6
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs6) : TheoremAStmt :=
  theoremA_of_refined5 L hSz hExc (P.toRefined5 L hSz)

theorem node_of_refined6
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs6) : NodeStatement :=
  node_of_refined5 L hSz hExc (P.toRefined5 L hSz)

end CFSG.CGT.Timmesfeld75
