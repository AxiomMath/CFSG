module

public import CFSG.CGT.Timmesfeld75.FinalReduced7
public import CFSG.CGT.Timmesfeld75.Sec7Nine
public import CFSG.CGT.Timmesfeld75.Sec6Two

public section

namespace CFSG.CGT.Timmesfeld75

structure Sec6Inputs : Prop where
  exotic : Sec62Exotic
  sec63 : Sec63
  sec66 : Sec66

structure Sec7Inputs : Prop where
  sec78 : Sec78
  sec710 : Sec710

structure RefinedStepInputs4 : Prop where
  a1 : StepA1Inputs2
  s511 : Step511Inputs
  step69 : Step69
  step68 : Step68
  step610 : Step610
  s6 : Sec6Inputs
  s7 : Sec7Inputs
  lemma26 : Lemma26Input
  step81 : Step81
  step82 : Step82

theorem RefinedStepInputs4.toRefined3
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs4) : RefinedStepInputs3 := by
  have hD := section3Dihedral_of_remaining L hSz hExc
  have hIso := section3IsoInput_of_remaining L hSz hD
  have h214 := lemma214_of_remaining L
  have h1 : Sec4NoA := sec4NoA_of_cases P.a1.caseI P.a1.caseIII
  have hA1 : StepA1 := stepA1_of h214 involutionClassInput_of_repo hIso L.aschbacherTheoremOne
    benderWCInput_of_repo h1 P.a1.nine P.a1.stepOne P.a1.corB P.a1.shult P.a1.yCase
  have h57 : Step57 := step57_of_stepA1 h214 involutionClassInput_of_repo
    L.aschbacherTheoremOne benderWCInput_of_repo hA1
  have h62 : Sec62 := sec62_of_exotic h1 P.s6.exotic
  exact
    { a1 := P.a1
      s511 := P.s511
      step69 := P.step69
      step68 := P.step68
      step610 := P.step610
      step79 := step79_of h214 involutionClassInput_of_repo hIso h57 P.lemma26 h1 h62
        P.s6.sec63 P.s6.sec66 P.s7.sec78
      step711 := step711_of h214 involutionClassInput_of_repo hIso h57 P.lemma26 h1 h62
        P.s6.sec63 P.s6.sec66 P.s7.sec710
      step81 := P.step81
      step82 := P.step82 }

theorem theoremA_of_refined4
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs4) : TheoremAStmt :=
  theoremA_of_refined3 L hSz hExc (P.toRefined3 L hSz hExc)

theorem node_of_refined4
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs4) : NodeStatement :=
  node_of_refined3 L hSz hExc (P.toRefined3 L hSz hExc)

end CFSG.CGT.Timmesfeld75
