module

public import CFSG.CGT.Timmesfeld75.FinalReduced11
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGold

public section

namespace CFSG.CGT.Timmesfeld75

structure Sec4CaseIInputs : Prop where
  trivialAction : Sec4I4TrivialAction
  outerAction : Sec4I4OuterAction
  outerAction5 : Sec4I5OuterAction
  goldschmidt : Sec4I5Goldschmidt

structure StepA1Inputs4 : Prop where
  caseI : Sec4CaseIInputs
  caseIIIEight : Sec4CaseIIIEight
  nine : Sec4Nine
  stepOne : Sec56StepOne
  corB : Sec56CorB
  shult : Sec57Shult
  yCase : Sec57Y

structure RefinedStepInputs8 : Prop where
  a1 : StepA1Inputs4
  s511 : Step511Inputs
  step69 : Step69
  corB : LargeExtraspecial.S8.TimmesfeldCorBInput
  ins68 : Sec68Inspection
  step610 : Step610
  s6 : Sec6Inputs2
  s7 : Sec7Inputs
  lemma26 : Lemma26Input
  step81 : Step81
  step82 : Step82

theorem RefinedStepInputs8.toRefined7
    (L : RemainingLiteratureInputs) (P : RefinedStepInputs8) :
    RefinedStepInputs7 where
  a1 :=
    { caseI := sec4CaseI_of_inputs (lemma214_of_remaining L) involutionClassInput_of_repo
        L.aschbacherTheoremOne benderWCInput_of_repo aschbacherNoPolarInput_of_repo
        P.a1.caseI.trivialAction P.a1.caseI.outerAction P.a1.caseI.outerAction5
        P.a1.caseI.goldschmidt
      caseIIIEight := P.a1.caseIIIEight
      nine := P.a1.nine
      stepOne := P.a1.stepOne
      corB := P.a1.corB
      shult := P.a1.shult
      yCase := P.a1.yCase }
  s511 := P.s511
  step69 := P.step69
  corB := P.corB
  ins68 := P.ins68
  step610 := P.step610
  s6 := P.s6
  s7 := P.s7
  lemma26 := P.lemma26
  step81 := P.step81
  step82 := P.step82

theorem theoremA_of_refined8
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs8) : TheoremAStmt :=
  theoremA_of_refined7 L hSz hExc (P.toRefined7 L)

theorem node_of_refined8
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs8) : NodeStatement :=
  node_of_refined7 L hSz hExc (P.toRefined7 L)

end CFSG.CGT.Timmesfeld75
