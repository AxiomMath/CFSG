module

public import CFSG.CGT.Timmesfeld75.FinalReduced10
public import CFSG.CGT.Timmesfeld75.Sec68FromCorB

public section

namespace CFSG.CGT.Timmesfeld75

structure RefinedStepInputs7 : Prop where
  a1 : StepA1Inputs3
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

theorem RefinedStepInputs7.toRefined6
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs7) : RefinedStepInputs6 := by
  have hD := section3Dihedral_of_remaining L hSz hExc
  have hIso := section3IsoInput_of_remaining L hSz hD
  have h214 := lemma214_of_remaining L
  have hIII : Sec4CaseIII := sec4CaseIII_of_inputs h214 involutionClassInput_of_repo hSz
    L.aschbacherTheoremOne benderWCInput_of_repo P.a1.caseIIIEight
  have h1 : Sec4NoA := sec4NoA_of_cases P.a1.caseI hIII
  have hA1 : StepA1 := stepA1_of h214 involutionClassInput_of_repo hIso L.aschbacherTheoremOne
    benderWCInput_of_repo h1 P.a1.nine P.a1.stepOne P.a1.corB P.a1.shult P.a1.yCase
  have h57 : Step57 := step57_of_stepA1 h214 involutionClassInput_of_repo
    L.aschbacherTheoremOne benderWCInput_of_repo hA1
  exact
    { a1 := P.a1
      s511 := P.s511
      step69 := P.step69
      corB68 := sec68CorB_of h57 P.corB P.ins68
      step610 := P.step610
      s6 := P.s6
      s7 := P.s7
      lemma26 := P.lemma26
      step81 := P.step81
      step82 := P.step82 }

theorem theoremA_of_refined7
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs7) : TheoremAStmt :=
  theoremA_of_refined6 L hSz hExc (P.toRefined6 L hSz hExc)

theorem node_of_refined7
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs7) : NodeStatement :=
  node_of_refined6 L hSz hExc (P.toRefined6 L hSz hExc)

end CFSG.CGT.Timmesfeld75
