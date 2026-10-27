module

public import CFSG.CGT.Timmesfeld75.FinalReduced12
public import CFSG.CGT.Timmesfeld75.Sec78

public section

namespace CFSG.CGT.Timmesfeld75

structure RefinedStepInputs9 : Prop where
  a1 : StepA1Inputs4
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

theorem RefinedStepInputs9.toRefined8
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (P : RefinedStepInputs9) : RefinedStepInputs8 := by
  have h214 := lemma214_of_remaining L
  have hIII : Sec4CaseIII := sec4CaseIII_of_inputs h214 involutionClassInput_of_repo hSz
    L.aschbacherTheoremOne benderWCInput_of_repo P.a1.caseIIIEight
  have hI : Sec4CaseI := sec4CaseI_of_inputs h214 involutionClassInput_of_repo
    L.aschbacherTheoremOne benderWCInput_of_repo aschbacherNoPolarInput_of_repo
    P.a1.caseI.trivialAction P.a1.caseI.outerAction P.a1.caseI.outerAction5
    P.a1.caseI.goldschmidt
  have h1 : Sec4NoA := sec4NoA_of_cases hI hIII
  have h62 : Sec62 := sec62_of_exotic h1 P.s6.exotic
  have h66 : Sec66 := sec66_of_three h62 P.s6.sec63 P.s6.three
  exact
    { a1 := P.a1
      s511 := P.s511
      step69 := P.step69
      corB := P.corB
      ins68 := P.ins68
      step610 := P.step610
      s6 := P.s6
      s7 := { sec78 := sec78_of h66 h1 h62 P.s6.sec63
              sec710 := P.sec710 }
      lemma26 := P.lemma26
      step81 := P.step81
      step82 := P.step82 }

theorem theoremA_of_refined9
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs9) : TheoremAStmt :=
  theoremA_of_refined8 L hSz hExc (P.toRefined8 L hSz)

theorem node_of_refined9
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hExc : Sec3TenExceptional) (P : RefinedStepInputs9) : NodeStatement :=
  node_of_refined8 L hSz hExc (P.toRefined8 L hSz)

end CFSG.CGT.Timmesfeld75
