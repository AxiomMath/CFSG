module

public import CFSG.CGT.Foote82.T66.Standard
public import CFSG.CGT.Foote82.T66.Climb
public import CFSG.CGT.Foote82.T66.MC2
public import CFSG.CGT.Foote82.T66.BranchB
public import CFSG.CGT.Foote82.T66.BranchA
public import CFSG.CGT.Foote82.T66.BranchASmall
public import CFSG.CGT.Foote82.T66.Faithful
public import CFSG.CGT.Foote82.T66.CitedProofs
public import CFSG.CGT.Foote82.T66.CaseII
public import CFSG.CGT.Foote82.T66.CaseI

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

theorem thm66FFaith_of_steps (hclimb : Climb66)
    (h5 : CFSG.ComponentClassification.GSThmB.AschbacherTheorem5Input)
    (hKG : CFSG.ComponentClassification.AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hgl : GlaubermanF) (hMC1 : CaseMC1) (hMC2 : CaseMC2) : Thm66FFaith := by
  refine thm66FFaith_of_noExtremal fun V _ _ _ G S L hE => ?_
  obtain ⟨s, hs⟩ := hE.exists_stdForm hclimb h5 hKG hgl
  have hsK : s ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
    have hsS : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
    refine ⟨hs.extremal.setup.S_le hsS, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have hcomp := hs.extremal.setup.component.1 hl
    exact ((Subgroup.mem_centralizer_iff.1 hcomp.2) s hsS).symm
  have h1 : 1 ≤ CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) :=
    CFSG.CGT.PushingUpLit.CGT6.Nine7.one_le_pRank_of_involution hsK hs.orderOf_s
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · exact hMC1 V G L s hs h.symm
  · exact hMC2 V G L s hs h

structure Thm66Named : Prop where
  aschbacherTheorem5 : CFSG.ComponentClassification.GSThmB.AschbacherTheorem5Input
  knownGroupFacts : CFSG.ComponentClassification.AschbacherKnownGroup.AschbacherKnownGroupFacts
  g8 : G8
  omegaMinusSixNormalizer : OmegaMinusSixNormalizer
  omegaMinusSixA6Centralizer : OmegaMinusSixA6Centralizer
  basThreeA6 : BASThreeA6
  basA6NoSix : BASA6NoSix
  basOmegaEight : BASOmegaEight
  basTIFails : BASTIFails
  basMaximal : BASMaximal
  frontierRankTwo : FrontierRankTwoF
  sporadicNoFComponent : SporadicNoFComponent
  footeLemma24 : FooteLemma24
  a11DoubleThreeCycle : A11DoubleThreeCycle
  a6NoSixDimIrr : A6NoSixDimIrr
  h1OmegaMinusSix : H1OmegaMinusSix
  h1OmegaMinusEight : H1OmegaMinusEight
  h1AltSevenFour : H1AltSevenFour
  h1ThreeAltSix : H1ThreeAltSix
  caseIISplit : CaseIISplit
  caseIIAut : CaseIIAut
  caseIIG1 : CaseIIG1
  caseIIG2 : CaseIIG2
  caseIIG9 : CaseIIG9
  caseIIG10 : CaseIIG10
  caseIIG12 : CaseIIG12
  caseIILemma511a : CaseIILemma511a
  caseIILemma511b : CaseIILemma511b
  caseIFooteLemma25 : CaseIFooteLemma25
  caseIG10 : CaseIG10
  caseILemma511 : CaseILemma511

theorem thm66F_of_named
    (h : Thm66Named) : Thm66F :=
  thm66F_of_faith
    (thm66FFaith_of_steps (climb66 schurAltLift_holds schurU42Lift_holds) h.aschbacherTheorem5
      h.knownGroupFacts glaubermanF_holds
      (caseMC1_of (lemma51 h.omegaMinusSixNormalizer h.omegaMinusSixA6Centralizer)
        (branchAFalse_of lemma52 (branchAAlt h.g8)
          (branchASmall h.basThreeA6 h.basA6NoSix h.basOmegaEight h.basTIFails h.basMaximal))
        (caseIFalse (lemma51 h.omegaMinusSixNormalizer h.omegaMinusSixA6Centralizer)
          h.caseIFooteLemma25 h.caseIG10 h.caseILemma511 schurU42Lift_holds)
        (caseIIFalse (lemma51 h.omegaMinusSixNormalizer h.omegaMinusSixA6Centralizer)
          h.caseIISplit h.caseIIAut h.caseIIG1 h.caseIIG2 h.caseIIG9 h.caseIIG10 h.caseIIG12
          h.caseIILemma511a h.caseIILemma511b))
      (caseMC2 h.frontierRankTwo h.sporadicNoFComponent h.footeLemma24 h.a11DoubleThreeCycle
        h.a6NoSixDimIrr))
    (thm66FNonFaith_holds h.h1OmegaMinusSix h.h1OmegaMinusEight h.h1AltSevenFour h.h1ThreeAltSix)

end CFSG.CGT.Foote82
