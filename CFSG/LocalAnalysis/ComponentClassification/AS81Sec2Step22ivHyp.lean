module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivStd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalM12
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalQuotNF
public import CFSG.StandardComponent.AschbacherSeitz.A5NoKProper
public import CFSG.ClassicalInvolution.Asc77.HypOmegaBasic
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Balance.LocalBalance
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Statements
public import CFSG.GH74.M12.HypT2
public import CFSG.GH74.M12.Reductions
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
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
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma39
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Boundary
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbFinal
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Timmesfeld.Moufang.Cases
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import CFSG.Walter.W67.W2Lemma26A
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

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Sec2Quot CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section Wsec

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
  (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
  (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (hW : IsElemAbelian 2 (sec2W A E y))
  (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E))
  (hW₁ : conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E ≤ sec2W A E y)

include h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hT hW₁

theorem rankTwoHyp_nbar (hn : ¬ (nbar (sec2W A E y) (sec2L A E)).Normal) :
    RankTwoHypNF (↥(normalizer (sec2W A E y : Set G)) ⧸
      (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G)))
      (nbar (sec2W A E y) (sec2L A E)) := by
  refine ⟨standardComponentIsStandard_nbar h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hT hW₁, hn,
    ?_⟩
  · refine SectionRank.le_pRank one_lt_two (E := nbar (sec2W A E y) R) (nbar_R_le_centralizer hF)
      (isElemAbelian_nbar hF.elemR) ?_
    rw [card_nbar_R h11 hE16 hF hL hodd hyA hyE hyU hy3 hW]
    norm_num

theorem false_of_nbar_not_normal (h310 : RankTwoClassical.Asc08Lemma310NF)
    (hA : ∀ X : Subgroup ((↥(normalizer (sec2W A E y : Set G)) ⧸
        (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G))) ⧸
        standardComponentOddCore (↥(normalizer (sec2W A E y : Set G)) ⧸
          (sec2W A E y).subgroupOf (normalizer (sec2W A E y : Set G)))),
      ¬ NativeSporadic.IsSporadic ↥X .M12 ∧ ¬ NativeSporadic.IsSporadic ↥X .J2)
    (hn : ¬ (nbar (sec2W A E y) (sec2L A E)).Normal) : False := by
  have hH := rankTwoHyp_nbar h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hT hW₁ hn
  obtain ⟨e⟩ := nonempty_rankTwoQuot_nbar_equiv h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hZ := odd_card_center_nbar h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hR := isSylowOf_nbar_R h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hR4 := card_nbar_R h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hR1 : nbar (sec2W A E y) R ≠ ⊥ := fun h => by
    rw [h, card_bot] at hR4
    omega
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hno : ∀ x, ¬ rightConjugate (nbar (sec2W A E y) R) x ≤ nbar (sec2W A E y) (sec2L A E) := by
    intro x hle
    have hmem : x⁻¹ * r * x ∈ rightConjugate (nbar (sec2W A E y) R) x := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hr
    have := hle hmem
    exact conj_not_mem_nbar h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hT hW₁ x⁻¹ hr hr1'
      (by simpa using this)
  rcases h310 _ _ (RankTwoClassical.NFQuot.rankTwoHyp_map hH)
      RankTwoSporadic.standardComponentOddCore_quotient_eq_bot
      ⟨(RankTwoClassical.NFQuot.quotCenterMap hH).symm.trans e⟩
      (RankTwoClassical.NFQuot.odd_card_center_map hH hZ) _
      (RankTwoClassical.NFQuot.isSylowOf_map hH hR)
      (RankTwoClassical.NFQuot.not_conj_le_map hH hR.isPGroup hno) with hJ | ⟨hM, -⟩
  · exact (hA _).2 hJ
  · exact (hA _).1 hM

end Wsec

end CFSG.ComponentClassification.AS81
