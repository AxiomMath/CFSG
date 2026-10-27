module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83G2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83E6Bound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIMultProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.RankTwoStandard

theorem step83_of_asc75
    (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4) (hPC : ExcPairCent) : Step83 := by
  intro G _ _ A hA hE
  have h34 : Asc08Lemma34 := asc08Lemma34
  obtain ⟨g, hg, R, T, hR, hT, -, -, hTR, -, -⟩ := section3Config_of h32 h33 h4 h34 G A hA
  have hc : Sec3 A R T g := ⟨hA, hR, hg, hT, commutator_eq_bot_iff_le_centralizer.mp hTR⟩
  have hperf : commutator ↥A = ⊤ := hA.standard.1.1
  rcases Nat.even_or_odd (Nat.card (center A)) with hev | hodd
  · rcases RankTwoExcHypII.excEvenMultiplier ↥A hperf hE hev with hG2 | hF4 | hE6
    · exact Step83Proof.odd_card_center_of_G2 h32 h4 h34 hc hG2
    · exact Step83Proof.odd_card_center_of_pair hPC h32 h4 h34 hc (Or.inl hF4)
        fun h => Step83Proof.centerElemFour_of_twistedE6 hperf h
    · exact Step83Proof.odd_card_center_of_pair hPC h32 h4 h34 hc (Or.inr hE6)
        fun h => Step83Proof.centerElemFour_of_twistedE6 hperf h
  · exact hodd

theorem step83_of
    (h32 : Lemma32) (h33 : Lemma33Three) (hPC : ExcPairCent) : Step83 :=
  step83_of_asc75 h32 h33 RankTwoFoundation.asc75Theorem4 hPC

end CFSG.ComponentClassification.RankTwoExceptional
