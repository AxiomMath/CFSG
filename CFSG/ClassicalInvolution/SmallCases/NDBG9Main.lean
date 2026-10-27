module

public import CFSG.ClassicalInvolution.SmallCases.NDBG9Cover
public import CFSG.ClassicalInvolution.SmallCases.NDBG5Use
public import CFSG.ClassicalInvolution.SmallCases.NDBG6Main
public import CFSG.ClassicalInvolution.SmallCases.NDBG8
public import CFSG.ClassicalInvolution.SmallCases.NDBCThird
public import CFSG.ClassicalInvolution.SmallCases.NDBD4Final
public import CFSG.ClassicalInvolution.SmallCases.NDBE7Frame
public import CFSG.ClassicalInvolution.Asc77.WP3S28WBoot
public import CFSG.ClassicalInvolution.Asc77.WP3S28BNDB
public import CFSG.ClassicalInvolution.Asc77.WP3CFCZT
import CFSG.ClassicalInvolution.Asc77.WP3SCVTag
import CFSG.ClassicalInvolution.Asc77.WP3SCVOrthC
import CFSG.ClassicalInvolution.Asc77.WP3SCUVCtx
import CFSG.ClassicalInvolution.Asc77.WP3ChainVGen3
import CFSG.ClassicalInvolution.Asc77.WP3SCUVertex
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3SCUModel4
import CFSG.ClassicalInvolution.Asc77.WP3SCURank
import CFSG.ClassicalInvolution.Asc77.WP3SCUNG
import CFSG.ClassicalInvolution.Asc77.WP3FrameBootNoTwins
import CFSG.ClassicalInvolution.Asc77.WP3SCRBoot
import CFSG.ClassicalInvolution.Asc77.AscFusionS14
import CFSG.ClassicalInvolution.Asc77.WP3SCUProved
import CFSG.ClassicalInvolution.Asc77.WP3SCSGenT
import CFSG.ClassicalInvolution.Asc77.WP3FrameStarE
import CFSG.ClassicalInvolution.Asc77.WP3FrameStar
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
import CFSG.ClassicalInvolution.Asc77.AscT3UMain
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRowsOuter
import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Outer
import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift
import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec
import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free
import CFSG.ClassicalInvolution.Balance.BootstrapExoticG2D4
import CFSG.ClassicalInvolution.Balance.BootstrapExoticE6
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
import CFSG.ClassicalInvolution.AschTight.Sec7L98J
import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

theorem chainFrames_noTriple :
    Asc77.FrameExistsOnE p f (Asc77.S28W.ChainShapeNoTriplePred (p := p) (f := f)) :=
  have hΩ := Asc77.hypOmegaModAll_of_fusionCore (Asc77.AscFusion.fusionCoreStmt p f)
  Asc77.S28W.chainFrame_exists_on_of_lemma52'W hΩ (Asc77.aEmptyChain_of_hypOmega hΩ)
    (Asc77.noTwinsChain_of_hypOmega hΩ) (Asc77.chainFrameGenT_proved p f)
    (Asc77.chainFrameHyp51t_proved p f) Asc77.lemma52

theorem twinFrames_weak : Asc77.FrameExistsOnE p f (TwinShapeWeakPred (p := p) (f := f)) :=
  twinFrame_exists_on_weak
    (Asc77.hypOmegaModAll_of_fusionCore (Asc77.AscFusion.fusionCoreStmt p f))
    G2D4Models.ih8G2D4_unconditional
    (Asc77.twinFrameHyp51_of (Asc77.T3CII.T3U.twinSmallInner_proved' (p := p))
      (Asc77.twinSmallOuter_of_d4 (G2D4Models.Twin.twinSmallOuterD4_of_fixLift p
        (fun e => G2D4Models.Twin.d4FixLift_proved (p := p) (f := e))))
      Asc77.g2d4VertexExcl_proved)
    Asc77.twinFrameGenT_proved

theorem noDataP1D_of_coverX (hcov : NoDataShapeCoverX p f)
    (hexo : Asc77.FrameExistsOnE p f (ExoticNoTwinPred p f)) : SmallConn.NoDataP1D p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow h3 h4 hD hB
  have hS : Setting p f K z := ⟨hnab, hp2, hq, hz, hBelow, h3, h4, hD, hB⟩
  by_cases hE : PSpEverywhere p f (𝒞 K)
  · exact pspCaseP1_proved p f G K z hS hE
  obtain ⟨L, hL, w, hw, hnot⟩ : ∃ L ∈ 𝒞 K, ∃ w : G, IsClassicalMember p f L w ∧
      ¬ PSpShape p f (𝒞 K) w := by
    by_contra hcon
    refine hE fun L hL w hw => ?_
    by_contra hn
    exact hcon ⟨L, hL, w, hw, hn⟩
  have hSL := hS.of_mem hL hw
  have e := conjClass_eq_of_mem hL
  obtain ⟨L₀, z₀, A, S, a, hfr, hA⟩ : ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G)
      (S : Set (Subgroup G)) (a : G),
      Asc77.FuzzyFrameDataStarE p f (𝒞 L) L₀ z₀ A S a ∧ Asc77.Hyp51 A := by
    rcases hcov G hnab hp2 hq L w hw hBelow h3 h4 hSL.dconn hSL.noBoot with
      ⟨A, hA⟩ | hsh | hsh | hsh | hsh
    · exact absurd hA (fuzzyFrameExcluded G L w hSL A)
    · exact chainFrames_noTriple G hnab hp2 hq L w hw hBelow hSL.dconn
        ⟨hsh, fun h => hSL.noBoot (Asc77.S28B.bootData_of_indepTriple h)⟩
    · exact twinFrames_weak G hnab hp2 hq L w hw hBelow hSL.dconn hsh
    · exact absurd (e ▸ hsh) hnot
    · exact hexo G hnab hp2 hq L w hw hBelow hSL.dconn hsh
  have hΩ := inClass_conjugates hw
  have h : ∀ M ∈ 𝒞 L, ∀ v : G, IsClassicalMember p f M v → LocalOddCentral (𝒞 L) {v} :=
    (Asc77.exactMembers_and_localOddCentral_of_fuzzyFrameStarE hnab hp2 hq hΩ
      (exists_single_class L) (localLieSystems_of_citBelowU hΩ hBelow) hSL.dconn hfr
      (Asc77.lemma52 G A hA)).2
  rw [e] at h
  exact h K (mem_conjClass_self K) z hz

theorem noDataBootD_of_coverX (hcov : NoDataShapeCoverX p f)
    (hexo : Asc77.FrameExistsOnE p f (ExoticNoTwinPred p f)) : SmallConn.NoDataBootD p f :=
  SmallConn.noDataBootD_of_noDataP1D exoticLeviBlock (noDataP1D_of_coverX hcov hexo)

variable (p f) in
@[expose] def ExoticFrameSpin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    ExoticBase p f K z → ¬ HasTwin p f K z →
      (∀ A : Subgroup G, ¬ Balance.Theorem5.FuzzyFrameOn p f (𝒞 K) A) →
        ∀ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily (𝒞 K) z) z, ∀ i,
          ((D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4)) →
            ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
              Asc77.FuzzyFrameDataStarE p f (𝒞 K) L₀ z₀ A S a ∧ Asc77.Hyp51 A

theorem exoticNoTwinFrames_of_spin (hspin : ExoticFrameSpin p f) :
    Asc77.FrameExistsOnE p f (ExoticNoTwinPred p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn ⟨hnoT, hnoF, D, i, hi⟩
  have hB : ExoticBase p f K z := ⟨hnab, hp2, hq, hz, hBelow, hconn⟩
  have hGD : ∀ h : D.tag i = .G2 ∨ D.tag i = .trialityD4,
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        Asc77.FuzzyFrameDataStarE p f (𝒞 K) L₀ z₀ A S a ∧ Asc77.Hyp51 A := by
    intro h
    by_cases h9 : p ^ f = 9
    · exact exoticFrameG2D4Nine_proved p f G K z hB hnoT hnoF h9 D i h
    · exact exoticFrameG2D4_proved p f G K z hB hnoT hnoF h9 D i h
  rcases hi with h | h | h | h
  · exact hGD (Or.inl h)
  · exact hGD (Or.inr h)
  · exact hspin G K z hB hnoT hnoF D i (Or.inl h)
  · exact hspin G K z hB hnoT hnoF D i (Or.inr h)

theorem noDataBootD_of_residualsX (hA : NoAllA1 p f) (hB' : NoG2D4Twin p f)
    (hexo : Asc77.FrameExistsOnE p f (ExoticNoTwinPred p f)) : SmallConn.NoDataBootD p f :=
  noDataBootD_of_coverX (noDataShapeCoverX_of_residuals hA hB' noD4Twins_proved) hexo

end CFSG.ClassicalInvolution.NDB
