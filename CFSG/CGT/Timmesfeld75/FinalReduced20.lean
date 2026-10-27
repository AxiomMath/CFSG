module

public import CFSG.CGT.Timmesfeld75.FinalReduced19
public import CFSG.CGT.Timmesfeld75.Sec56OneMain
public import CFSG.CGT.Timmesfeld75.FinalReduced17

public section

namespace CFSG.CGT.Timmesfeld75

structure StepA1Inputs8 : Prop where
  caseI : Sec4CaseIInputs2
  caseIIIEight : Sec4CaseIIIEight
  nine : Sec4Nine
  corB : Sec56CorB
  shult : Sec57Shult

structure RefinedStepInputs16 : Prop where
  a1 : StepA1Inputs8
  a6Klein : A6KleinOrbit
  s511 : Step511Inputs
  step69 : Step69
  corB : LargeExtraspecial.S8.TimmesfeldCorBInput
  ins68 : Sec68Inspection
  step610 : Step610
  s6 : Sec6Inputs5
  sec710 : Sec710
  lemma26 : Lemma26Input
  step81 : Step81
  step82 : Step82

theorem RefinedStepInputs16.toRefined10
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (P : RefinedStepInputs16) : RefinedStepInputs10 := by
  have h215 : Lemma215Stmt :=
    lemma215_of_literature (LiteratureInputs.of_reduced (ReducedLiteratureInputs.of_remaining L))
  have h1 : Sec4NoA := sec4NoA_of_inputs L hSz P.lemma26 P.a1.caseI P.a1.caseIIIEight
  exact
    { a1 :=
        { caseI := P.a1.caseI
          caseIIIEight := P.a1.caseIIIEight
          nine := P.a1.nine
          stepOne := sec56StepOne_proved h215 P.lemma26 P.a6Klein L.aschbacherTheoremOne
            benderWCInput_of_repo
          corB := P.a1.corB
          shult := P.a1.shult
          yCase := sec57Y_proved h215 P.lemma26 }
      s511 := P.s511
      step69 := P.step69
      corB := P.corB
      ins68 := P.ins68
      step610 := P.step610
      s6 :=
        { exotic := sec62Exotic_of_big h1 P.s6.exotic
          sec63 := sec63_of_a6 h215 P.lemma26 (sec48_of_noA h1)
            (sec62_of_big h1 P.s6.exotic) P.s6.a6
          three := P.s6.three }
      sec710 := P.sec710
      lemma26 := P.lemma26
      step81 := P.step81
      step82 := P.step82 }

theorem theoremA_of_refined16
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (P : RefinedStepInputs16) : TheoremAStmt :=
  theoremA_of_refined10 L hSz sec3TenExceptional (P.toRefined10 L hSz)

theorem node_of_refined16
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (P : RefinedStepInputs16) : NodeStatement :=
  node_of_refined10 L hSz sec3TenExceptional (P.toRefined10 L hSz)

end CFSG.CGT.Timmesfeld75
