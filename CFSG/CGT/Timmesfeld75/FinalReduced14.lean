module

public import CFSG.CGT.Timmesfeld75.FinalReduced13
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJMain

public section

namespace CFSG.CGT.Timmesfeld75

structure Sec4CaseIInputs2 : Prop where
  rootGroup : Sec4I4RootGroupInput
  outerAction : Sec4I4OuterAction
  outerAction5 : Sec4I5OuterAction
  goldschmidt : Sec4I5Goldschmidt

structure StepA1Inputs5 : Prop where
  caseI : Sec4CaseIInputs2
  caseIIIEight : Sec4CaseIIIEight
  nine : Sec4Nine
  stepOne : Sec56StepOne
  corB : Sec56CorB
  shult : Sec57Shult
  yCase : Sec57Y

structure RefinedStepInputs10 : Prop where
  a1 : StepA1Inputs5
  s511 : Step511Inputs
  step69 : Step69
  corB : LargeExtraspecial.S8.TimmesfeldCorBInput
  ins68 : Sec68Inspection
  step610 : Step610
  s6 : Sec6Inputs2
  sec710 : Sec710
  lemma26 : Lemma26Input
  step81 : Step81
  step82 : Step82

theorem RefinedStepInputs10.toRefined9
    (L : RemainingLiteratureInputs) (P : RefinedStepInputs10) :
    RefinedStepInputs9 where
  a1 :=
    { caseI :=
        { trivialAction := sec4I4TrivialAction_of_inputs aschbacherNoPolarInput_of_repo
            (lemma215_of_literature
              (LiteratureInputs.of_reduced (ReducedLiteratureInputs.of_remaining L)))
            P.lemma26 P.a1.caseI.rootGroup
          outerAction := P.a1.caseI.outerAction
          outerAction5 := P.a1.caseI.outerAction5
          goldschmidt := P.a1.caseI.goldschmidt }
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
  sec710 := P.sec710
  lemma26 := P.lemma26
  step81 := P.step81
  step82 := P.step82

theorem theoremA_of_refined10
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs10) : TheoremAStmt :=
  theoremA_of_refined9 L hSz hExc (P.toRefined9 L)

theorem node_of_refined10
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs10) : NodeStatement :=
  node_of_refined9 L hSz hExc (P.toRefined9 L)

end CFSG.CGT.Timmesfeld75
