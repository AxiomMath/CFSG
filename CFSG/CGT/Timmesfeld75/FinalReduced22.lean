module

public import CFSG.CGT.Timmesfeld75.FinalReduced21

public section

namespace CFSG.CGT.Timmesfeld75

structure RefinedStepInputs18 : Prop where
  a1 : StepA1Inputs8
  s511 : Step511Inputs
  step69 : Step69
  corB : LargeExtraspecial.S8.TimmesfeldCorBInput
  ins68 : Sec68Inspection
  step610 : Step610
  s6 : Sec6Inputs6
  sec710 : Sec710
  lemma26 : Lemma26Input
  step81 : Step81
  step82 : Step82

theorem RefinedStepInputs18.toRefined17 (P : RefinedStepInputs18) : RefinedStepInputs17 :=
  { a1 := P.a1
    a6Klein := a6KleinOrbit
    s511 := P.s511
    step69 := P.step69
    corB := P.corB
    ins68 := P.ins68
    step610 := P.step610
    s6 := P.s6
    sec710 := P.sec710
    lemma26 := P.lemma26
    step81 := P.step81
    step82 := P.step82 }

theorem theoremA_of_refined18
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (P : RefinedStepInputs18) : TheoremAStmt :=
  theoremA_of_refined17 L hSz P.toRefined17

theorem node_of_refined18
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (P : RefinedStepInputs18) : NodeStatement :=
  node_of_refined17 L hSz P.toRefined17

end CFSG.CGT.Timmesfeld75
