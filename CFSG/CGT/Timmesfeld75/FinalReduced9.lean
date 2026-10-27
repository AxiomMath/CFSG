module

public import CFSG.CGT.Timmesfeld75.FinalReduced8
public import CFSG.CGT.Timmesfeld75.Sec66
public import CFSG.CGT.Timmesfeld75.Sec68

public section

namespace CFSG.CGT.Timmesfeld75

structure Sec6Inputs2 : Prop where
  exotic : Sec62Exotic
  sec63 : Sec63
  three : Sec66Three

structure RefinedStepInputs5 : Prop where
  a1 : StepA1Inputs2
  s511 : Step511Inputs
  step69 : Step69
  corB68 : Sec68CorB
  step610 : Step610
  s6 : Sec6Inputs2
  s7 : Sec7Inputs
  lemma26 : Lemma26Input
  step81 : Step81
  step82 : Step82

theorem RefinedStepInputs5.toRefined4
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs5) : RefinedStepInputs4 := by
  have hD := section3Dihedral_of_remaining L hSz hExc
  have hIso := section3IsoInput_of_remaining L hSz hD
  have h214 := lemma214_of_remaining L
  have h1 : Sec4NoA := sec4NoA_of_cases P.a1.caseI P.a1.caseIII
  have hA1 : StepA1 := stepA1_of h214 involutionClassInput_of_repo hIso L.aschbacherTheoremOne
    benderWCInput_of_repo h1 P.a1.nine P.a1.stepOne P.a1.corB P.a1.shult P.a1.yCase
  have h57 : Step57 := step57_of_stepA1 h214 involutionClassInput_of_repo
    L.aschbacherTheoremOne benderWCInput_of_repo hA1
  have h62 : Sec62 := sec62_of_exotic h1 P.s6.exotic
  have h66 : Sec66 := sec66_of_three h62 P.s6.sec63 P.s6.three
  exact
    { a1 := P.a1
      s511 := P.s511
      step69 := P.step69
      step68 := step68_of h214 involutionClassInput_of_repo hIso h57 h1 P.s6.sec63 P.corB68
      step610 := P.step610
      s6 := { exotic := P.s6.exotic, sec63 := P.s6.sec63, sec66 := h66 }
      s7 := P.s7
      lemma26 := P.lemma26
      step81 := P.step81
      step82 := P.step82 }

theorem theoremA_of_refined5
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs5) : TheoremAStmt :=
  theoremA_of_refined4 L hSz hExc (P.toRefined4 L hSz hExc)

theorem node_of_refined5
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs5) : NodeStatement :=
  node_of_refined4 L hSz hExc (P.toRefined4 L hSz hExc)

end CFSG.CGT.Timmesfeld75
