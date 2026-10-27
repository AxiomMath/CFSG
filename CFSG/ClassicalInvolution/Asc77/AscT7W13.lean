module

public import CFSG.ClassicalInvolution.Asc77.AscT7JFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7K11
public import CFSG.ClassicalInvolution.Asc77.AscT7ERFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7DRFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RL
public import CFSG.ClassicalInvolution.Asc77.AscT7RH
public import CFSG.ClassicalInvolution.Asc77.AscT7HS5
public import CFSG.ClassicalInvolution.Asc77.AscT7HFinal
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SCall
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpModel
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuModel
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RInnerSL
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Inner
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Outer
public import CFSG.ClassicalInvolution.Asc77.AscT7NI
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Main
public import CFSG.ClassicalInvolution.Asc77.AscT7MOrth
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Fin
public import CFSG.ClassicalInvolution.Asc77.AscT7L15
public import CFSG.ClassicalInvolution.Asc77.AscT7L25
public import CFSG.ClassicalInvolution.Asc77.AscT7Y3
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRows
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRowsOuter
public import CFSG.ClassicalInvolution.Asc77.AscE18FromM
public import CFSG.ClassicalInvolution.Asc77.AscT7AFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7ASectD
public import CFSG.ClassicalInvolution.Asc77.AscT7CFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7EFinal3
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Frat
public import CFSG.ClassicalInvolution.Asc77.AscT7NB
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main
public import CFSG.GH74.GLS.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Open.QuasithinDefs
public import CFSG.StronglyEmbedded.UniqueCoset
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Walter.J1
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false


variable {p f : ℕ} [Fact p.Prime]

theorem twinSmallInner_rows_proved (p : ℕ) [Fact p.Prime] : TwinSmallInner p :=
  twinSmallInner_of_rows (twinSmallInnerSp p) (twinSmallInnerSL p) (twinSmallInnerSU p)
    (G2D4Models.Twin.twinSmallInnerD4 p)

theorem twinSmallOuter_rows_proved (p : ℕ) [Fact p.Prime] : TwinSmallOuter p :=
  twinSmallOuter_of_d4 (G2D4Models.Twin.twinSmallOuterD4_of_fixLift p
    (fun e => G2D4Models.Twin.d4FixLift_proved (p := p) (f := e)))

theorem thm7A_of_inputs₁₃
    (hconn : C21_14_Y_conn_W p f)
    (hres : TwinSqOrth p) (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    (hgen22 : C22_8Gen p f) (hZ : Hyp22ZStarCu p f) (hchain22 : C22_chainSettingX p f)
    (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h11 : C25_11 p f) (h16 : C25_16 p f) (h20 : C25_20_ex p f) : Thm7A p f := by
  intro G _ _ _ Ω K hst htw hdis
  have hNT := CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all (p := p)
  have hHt : TwinFrameHyp51t p f := twinFrameHyp51t_proved (twinSmallInner_rows_proved p)
  have hHu : TwinFrameHyp51u p f := twinFrameHyp51u_proved (twinSmallOuter_rows_proved p)
  have hC3 := c21_3_of_hyp51 hHt hHu
  have hY := c21_14_Y_disc_of_hyp51 hHt hHu
  have hNC := c21_normCent_of_conn_W hHt hHu hconn
  exact (thm7A_of_steps (wz p f)
    (c21_2_final_residual p f hNT hHt hHu (c21_13_M_ne_of_c21_3 hC3)
      (c21_14_N_disc_of_Ydisc hC3 hY) (c21_14_alt_rest_of hC3 hY hNC)
      (c21_15_of_normCent hC3 hNC) (c21_starCent_proved p f))
    (c22_1_of_inputsX (thmEWithSylow_of_nonToral f hNT) (hyp22Hyp51z p f)
      (hyp22Hyp51u_of_fourthTwin (twinSqAlphaRows_of_orth p hres)
        (hyp22FourthTwin_of_fourTwins h4))
      (c22_4_sigma_proved p f) (c22_4_cent_of_zstar hZ) (c22_8X_of_inputs h4 hF hgen22) hchain22)
    (c23_1_of thompsonCube thompsonStar c23_1_clique_proved)
    (c23_3_of_inputsK (thmEWithSylow_of_nonToral f hNT) (c23_2_trans_proved p f)
      (c23_setupSetting_proved p f) c23_4X_proved c23_5X_type_proved c23_7_proved c23_GammaU_proved
      c23_9_noZX_proved c23_9_genX_proved hchain23
      (CFSG.ClassicalInvolution.RouteD.spinMinus6Generated_galois hst.odd))
    (c24_1_of_core hcore hbig hpair)
    (c25_E4_of_idx (c25_17_idx_of_11_16 p f h11 h16) (T7G2.c25_20_of_ex h11 h16 h20)))
    G Ω K hst htw hdis

end CFSG.ClassicalInvolution.Asc77
