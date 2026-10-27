module

public import CFSG.CGT.Timmesfeld75.FinalReduced20
public import CFSG.CGT.Timmesfeld75.A6KleinProof

public section

namespace CFSG.CGT.Timmesfeld75

structure Sec6Inputs6 : Prop where
  exotic : Sec62ExoticBig
  a6 : Sec63A6

structure RefinedStepInputs17 : Prop where
  a1 : StepA1Inputs8
  a6Klein : A6KleinOrbit
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

theorem RefinedStepInputs17.toRefined16
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (P : RefinedStepInputs17) : RefinedStepInputs16 := by
  have h215 : Lemma215Stmt :=
    lemma215_of_literature (LiteratureInputs.of_reduced (ReducedLiteratureInputs.of_remaining L))
  have h1 : Sec4NoA := sec4NoA_of_inputs L hSz P.lemma26 P.a1.caseI P.a1.caseIIIEight
  have h62 : Sec62 := sec62_of_big h1 P.s6.exotic
  have h63 : Sec63 := sec63_of_a6 h215 P.lemma26 (sec48_of_noA h1) h62 P.s6.a6
  have h66 : Sec66 := sec66_of_inputs h215 P.lemma26 h62 h63
  exact
    { a1 := P.a1
      a6Klein := P.a6Klein
      s511 := P.s511
      step69 := P.step69
      corB := P.corB
      ins68 := P.ins68
      step610 := P.step610
      s6 :=
        { exotic := P.s6.exotic
          a6 := P.s6.a6
          three := fun G _ T T₁ n m hc _ => h66 G T T₁ n m hc }
      sec710 := P.sec710
      lemma26 := P.lemma26
      step81 := P.step81
      step82 := P.step82 }

theorem theoremA_of_refined17
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (P : RefinedStepInputs17) : TheoremAStmt :=
  theoremA_of_refined16 L hSz (P.toRefined16 L hSz)

theorem node_of_refined17
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (P : RefinedStepInputs17) : NodeStatement :=
  node_of_refined16 L hSz (P.toRefined16 L hSz)

end CFSG.CGT.Timmesfeld75
