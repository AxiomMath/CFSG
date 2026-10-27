module

public import CFSG.CGT.Timmesfeld75.FinalReduced6
public import CFSG.CGT.Timmesfeld75.Sec3Ten
public import CFSG.CGT.Timmesfeld75.Sec4NoAAssembly

public section

namespace CFSG.CGT.Timmesfeld75

structure StepA1Inputs2 : Prop where
  caseI : Sec4CaseI
  caseIII : Sec4CaseIII
  nine : Sec4Nine
  stepOne : Sec56StepOne
  corB : Sec56CorB
  shult : Sec57Shult
  yCase : Sec57Y

structure RefinedStepInputs3 : Prop where
  a1 : StepA1Inputs2
  s511 : Step511Inputs
  step69 : Step69
  step68 : Step68
  step610 : Step610
  step79 : Step79
  step711 : Step711
  step81 : Step81
  step82 : Step82

theorem RefinedStepInputs3.toRefined2
    (P : RefinedStepInputs3) : RefinedStepInputs2 where
  a1 :=
    { noA := sec4NoA_of_cases P.a1.caseI P.a1.caseIII
      nine := P.a1.nine
      stepOne := P.a1.stepOne
      corB := P.a1.corB
      shult := P.a1.shult
      yCase := P.a1.yCase }
  s511 := P.s511
  step69 := P.step69
  step68 := P.step68
  step610 := P.step610
  step79 := P.step79
  step711 := P.step711
  step81 := P.step81
  step82 := P.step82

theorem section3Dihedral_of_remaining
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) : Section3DihedralInput :=
  section3Dihedral (lemma214_of_remaining L) involutionClassInput_of_repo hSz
    L.aschbacherTheoremOne benderWCInput_of_repo hExc

theorem theoremA_of_refined3
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs3) : TheoremAStmt :=
  theoremA_of_refined2 L hSz (section3Dihedral_of_remaining L hSz hExc) P.toRefined2

theorem node_of_refined3
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs3) : NodeStatement :=
  node_of_refined2 L hSz (section3Dihedral_of_remaining L hSz hExc) P.toRefined2

end CFSG.CGT.Timmesfeld75
