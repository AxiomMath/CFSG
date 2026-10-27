module

public import CFSG.CGT.Timmesfeld75.FinalReduced22
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGLayer
public import CFSG.CGT.T75K.Exotic
public import CFSG.CGT.T75B.Outer
public import CFSG.CGT.T75B.Lemma21Wire
public import CFSG.CGT.T75L.Outer5
public import CFSG.CGT.T75H.Assemble
public import CFSG.CGT.T75I.BenderDisc
public import CFSG.CGT.T75I.JankoCtx
public import CFSG.CGT.T75P.Assemble
public import CFSG.CGT.T75N.L29Generic
public import CFSG.CGT.T75F.E710Glue
public import CFSG.CGT.T75Q.Odd82
public import CFSG.CGT.T75P.Odd81
public import CFSG.CGT.T75R.Final
public import CFSG.CGT.T75R.TriAProof
public import CFSG.CGT.T75H.PartB

public section

namespace CFSG.CGT.Timmesfeld75

structure NodeInputs : Prop where
  aschbacherTheoremOne : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne
  goldschmidt : Goldschmidt1974
  corB : LargeExtraspecial.S8.TimmesfeldCorBInput
  benderCenter : BenderCenterInput
  unitaryTwoGeneration : UnitaryTwoGenerationInput
  lemma26 : Lemma26Input
  rootGroup : Sec4I4RootGroupInput
  shult : Sec57Shult
  corB56 : Sec56CorB
  ins68 : Sec68Inspection
  listWC : ListWCIdentification
  a9 : A9Input
  small64 : Small64Input
  szThree : Section3SzInput
  noLayer : Sec4I5NoLayer
  a6 : Sec63A6
  jankoM22 : CFSG.CGT.T75I.JankoM22CtxInput
  jankoM23 : CFSG.CGT.T75I.JankoM23CtxInput
  a8Sylow : CFSG.CGT.T75P.A8SylowInput
  m24Sylow : CFSG.CGT.T75P.M24SylowInput

theorem NodeInputs.toRemaining (I : NodeInputs) : RemainingLiteratureInputs :=
  { aschbacherTheoremOne := I.aschbacherTheoremOne
    benderCenter := I.benderCenter
    unitaryTwoGeneration := I.unitaryTwoGeneration }

theorem NodeInputs.toRefined18
    (hM : MultPrimeInput) (hA : AltCoverInput) (I : NodeInputs) : RefinedStepInputs18 :=
  have hAsc : AschbacherNoPolarInput := aschbacherNoPolarInput_of_repo
  have h215 : Lemma215Stmt :=
    lemma215_of_literature (LiteratureInputs.of_reduced (ReducedLiteratureInputs.of_remaining
      I.toRemaining))
  have hA4 : Sec4I4TrivialAction :=
    sec4I4TrivialAction_of_inputs hAsc h215 I.lemma26 I.rootGroup
  have hW : ∀ (f : ℕ) (P : Type) [Group P] [Finite P], 2 ≤ f →
      (P ≃* CFSG.Theory.Comparator.PSU3Model f) → CFSG.CGT.T75B.Lemma21Input P :=
    fun _ _ _ _ hf e => CFSG.CGT.T75B.lemma21Input_of_mulEquiv hf e
  have hC4 : Sec4I4OuterAction :=
    CFSG.CGT.T75B.sec4I4OuterAction_of hAsc h215 I.lemma26 I.rootGroup hA4 hW
  have hCaseI : Sec4CaseIInputs2 :=
    { rootGroup := I.rootGroup
      outerAction := hC4
      outerAction5 := CFSG.CGT.T75L.sec4I5OuterAction_of hAsc hA4 hC4 hW
      goldschmidt := sec4I5Goldschmidt_of_noLayer I.goldschmidt I.noLayer }
  have hEight : Sec4CaseIIIEight :=
    T75R.sec4CaseIIIEight_of_triA (lemma214_of_remaining I.toRemaining) involutionClassInput_of_repo
        I.szThree I.aschbacherTheoremOne benderWCInput_of_repo T75R.triA
  have hNoA : Sec4NoA :=
    sec4NoA_of_inputs I.toRemaining I.szThree I.lemma26 hCaseI hEight
  have hIso : Section3IsoInput :=
    section3IsoInput_of_remaining I.toRemaining I.szThree
      (section3Dihedral_of_remaining I.toRemaining I.szThree sec3TenExceptional)
  have h62 : Sec62 := sec62_of_big hNoA (CFSG.CGT.T75K.sec62ExoticBig_of_noA hNoA)
  have h63 : Sec63 := sec63_of_a6 h215 I.lemma26 (sec48_of_noA hNoA) h62 I.a6
  have h66 : Sec66 := sec66_of_inputs h215 I.lemma26 h62 h63
  have hA1 : StepA1 := stepA1_of (lemma214_of_remaining I.toRemaining) involutionClassInput_of_repo
    hIso I.aschbacherTheoremOne benderWCInput_of_repo hNoA (sec4Nine_of_noA hNoA)
    (sec56StepOne_proved h215 I.lemma26 a6KleinOrbit I.aschbacherTheoremOne benderWCInput_of_repo)
    I.corB56 I.shult (sec57Y_proved h215 I.lemma26)
  have h57 : Step57 := step57_of_stepA1 (lemma214_of_remaining I.toRemaining)
    involutionClassInput_of_repo I.aschbacherTheoremOne benderWCInput_of_repo hA1
  { a1 :=
      { caseI := hCaseI
        caseIIIEight := hEight
        nine := sec4Nine_of_noA hNoA
        corB := I.corB56
        shult := I.shult }
    s511 :=
      { listWC := I.listWC
        a9 := I.a9
        altCover := hA
        mult := hM
        small64 := I.small64
        lemma29 := CFSG.CGT.T75N.lemma29StdInput }
    step69 := CFSG.CGT.T75H.step69_of_noGlauberman (lemma214_of_remaining I.toRemaining)
      involutionClassInput_of_repo hIso hNoA h63 h57
      (CFSG.CGT.T75H.step69Rank2_of (lemma214_of_remaining I.toRemaining)
        involutionClassInput_of_repo hIso hNoA h63 h57 h215 I.listWC
        CFSG.CGT.T75I.aschbacherDisconnectedInput_of_repo
        (CFSG.CGT.T75H.step69PartB_of (lemma214_of_remaining I.toRemaining)
          involutionClassInput_of_repo hIso hNoA h63 h57 h215 I.listWC
          CFSG.CGT.T75I.aschbacherDisconnectedInput_of_repo))
    corB := I.corB
    ins68 := I.ins68
    step610 := CFSG.CGT.T75I.step610_of_janko_ctx I.jankoM22 I.jankoM23
      (lemma214_of_remaining I.toRemaining) involutionClassInput_of_repo hIso h57 hNoA h62 h63
      CFSG.CGT.T75I.aschbacherDisconnectedInput_of_repo
    s6 := { exotic := CFSG.CGT.T75K.sec62ExoticBig_of_noA hNoA, a6 := I.a6 }
    sec710 := CFSG.CGT.T75F.sec710_of I.goldschmidt I.aschbacherTheoremOne h66 hNoA h62 h63
    lemma26 := I.lemma26
    step81 := CFSG.CGT.T75P.step81_of_odd (lemma214_of_remaining I.toRemaining)
      involutionClassInput_of_repo hIso hNoA h62 h63 h66
      (CFSG.CGT.T75P.odd81_of_inputs (lemma214_of_remaining I.toRemaining)
        involutionClassInput_of_repo hIso hNoA h62 h63 h66 h215 I.listWC) I.a8Sylow
    step82 := CFSG.CGT.T75P.step82_of_odd
      (CFSG.CGT.T75Q.odd82_of_inputs (lemma214_of_remaining I.toRemaining)
        involutionClassInput_of_repo hIso hNoA h62 h63 h66 h215 I.listWC) I.m24Sylow }

theorem theoremA_of_flat (hM : MultPrimeInput) (hA : AltCoverInput) (I : NodeInputs) :
    TheoremAStmt :=
  theoremA_of_refined18 I.toRemaining I.szThree (I.toRefined18 hM hA)

theorem node_of_flat (hM : MultPrimeInput) (hA : AltCoverInput) (I : NodeInputs) :
    NodeStatement :=
  node_of_refined18 I.toRemaining I.szThree (I.toRefined18 hM hA)

end CFSG.CGT.Timmesfeld75
