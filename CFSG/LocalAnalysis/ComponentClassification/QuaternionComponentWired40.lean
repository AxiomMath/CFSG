module

public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired36
public import CFSG.ClassicalInvolution.Q3.TL4LieZ2Model
public import CFSG.ClassicalInvolution.Q3.TL4S289GenC
public import CFSG.ClassicalInvolution.Q3.TL4S289GenD3
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2S
public import CFSG.ClassicalInvolution.Q3.TL4Mdl264O
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinWiredFields
public import CFSG.ClassicalInvolution.Q3.TL4C263E4
public import CFSG.ClassicalInvolution.Q3.TL4C264NoE4
public import CFSG.ClassicalInvolution.Q3.TL4C264Om
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2W
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2F
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscC
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2
public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521
public import CFSG.ClassicalInvolution.Q3.TL4Thm5SmallL3U3
public import CFSG.ClassicalInvolution.Q3.TL4Thm5Step
public import CFSG.ClassicalInvolution.Q3.TL4TwistTw
public import CFSG.ClassicalInvolution.Q3.TL4WylE7
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentPow
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired31

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

structure WiredInputs₄₀ : Prop where
  gh74 : GH74SectionalModels
  frameAEmptyP : Q3.PhilipHall.Frame.FrameAEmptyPf.FrameAEmptyP
  cLeafE8 : Q3.TC.Thin.CLeafE8 3 (Q3.TC.Thin.PackIH 3)
  cLeafE64 : Q3.TC.Thin.CLeafE64 3 (Q3.TC.Thin.PackIH 3)
  cLeafE29 : Q3.TC.Thin.CLeafE29 3 (Q3.TC.Thin.PackIH 3)
  cLeafAE : Q3.TC.Thin.CLeafAE 3 (Q3.TC.Thin.PackIH 3)
  dLeafE4 : Q3.TC.Thin.DLeafE4 3 (Q3.TC.Thin.PackIH 3)
  dLeafStar : Q3.TC.Thin.DLeafStar 3 (Q3.TC.Thin.PackIH 3)
  dLeafEnd : Q3.TC.Thin.DLeafEnd 3 (Q3.TC.Thin.PackIH 3)
  twinThin : ∀ n, Q3.CIT3Below n → Q3.TL4.TightBelowRPlus 3 n →
    Q3.PhilipHall.Frame.TwinThinInput n
  pfTables : Q3.PhilipHall.Frame.Twin1711.PfTables
  twinDiscPerpSP : ∀ n, Q3.PhilipHall.Frame.TwinCoreDiscPerpSP n
  twinPerpSE : ∀ n, Q3.CIT3Below n → Q3.TL4.TightBelowRPlus 3 n →
    Q3.PhilipHall.Frame.TwinCorePerpSE' n
  model1524Om : Q3.TL4.Model1524Twin3Om
  linkZ2L2Outer : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightLinkZ2L2OuterR n
  linkZ2L2Inner : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightLinkZ2L2InnerR n
  linkEdgeOdd : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.LinkDisc.TightLinkEdgeRigidR n

section Wired

theorem WiredInputs₄₀.twinConnSE
    (h : WiredInputs₄₀) (n : ℕ) :
    Q3.CIT3Below n → Q3.TL4.TightBelowRPlus 3 n → Q3.PhilipHall.Frame.TwinCoreConnSE' n :=
  fun hA hP => Q3.PhilipHall.Frame.twinCoreConnSE'_of_pfOut
    Q3.PhilipHall.Frame.TwinCentRes.modelFactSp62
    Q3.PhilipHall.Frame.TwinCentRes.modelFactD42_of_cert
    Q3.PhilipHall.Frame.TwinCentRes.modelFactM12_of_certs
    (Q3.PhilipHall.Frame.twinConnPreludeOut_proved n hA hP)
    (Q3.PhilipHall.Frame.twinConnEdgesOut_proved n hA hP) (h.twinThin n hA hP)
    (Q3.PhilipHall.Frame.twinE4Perfect_proved n hA hP) h.pfTables

theorem WiredInputs₄₀.twin
    (h : WiredInputs₄₀) : ∀ n, Q3.TL4.TwinStepR 3 n := fun n hA hP =>
  Q3.PhilipHall.Frame.twinStepRSE_of_cases (h.twinConnSE n) (h.twinDiscPerpSP n)
    (h.twinPerpSE n) (hP.twin rfl) hA hP

theorem clique5₄₀
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightSec5CliqueR n := fun hA hP =>
  Q3.TL4.tightSec5CliqueR_of_plus hA hP (thm4RBelow₂₇ n hA hP) Q3.TL4.secIdE2Clique5_proved
    (Q3.TL4.secIdE4NoClique5_of_graphFacts e4QuatGraphFacts_of_exLie₂₅)
    Q3.TL4.secIdLieClique5_proved

theorem triangle₄₀
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightSecTriangleR n := fun hA hP =>
  Q3.TL4.tightSecTriangleR_of_plus hA hP (thm4RBelow₂₇ n hA hP) Q3.TL4.secIdE2Triangle_proved
    (Q3.TL4.secIdE4DStar_of_graphFacts e4QuatGraphFacts_of_exLie₂₅)
    Q3.TL4.secIdLieTriangle_proved

theorem hyp51₄₀
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightHyp51TriR n := fun hA hP =>
  Q3.TL4.tightHyp51TriR_three_of_components (thm4RBelow₂₇ n hA hP) hP.thm5 (hP.twin rfl).toSet

theorem c26_13₄₀
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightC26_13R n := fun hA hP =>
  Q3.TL4.tightC26_13R_of_caseB (Q3.TL4.tightC27_4MR_of (clique5₄₀ n hA hP))
    Q3.TL4.tightBenderEndR (thm4RBelow₂₇ n hA hP)
    (Q3.TL4.tightC27_YsmallR_of (secNoRoot₂₇ n hA hP) (triangle₄₀ n hA hP))
    (alphaFrame₂₇ n hA hP) (hyp51₄₀ n hA hP)
    (Q3.TL4.tightW2CaseBR_three_of hA hP (thm4RBelow₂₇ n hA hP) (alphaFrame₂₇ n hA hP)
      (hyp51₄₀ n hA hP))

theorem connR'₄₀
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightConnLeafR' n :=
  Q3.TL4.connLeafR'_of_residuals₇ (s26Dich₂₇ n) (c26_13₄₀ n) (clique5₄₀ n)
    Q3.TL4.tightBenderEndR (e4SecGen₂₇ n) (lambdaComm₃₁ n) (triangle₄₀ n) (thm4RBelow₂₇ n)
    (hyp51₄₀ n) (alphaFrame₂₇ n) (secNoRoot₂₇ n)

theorem linkZ2Alpha₄₀
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightLinkZ2AlphaR n := fun hA hP =>
  Q3.TL4.tightLinkZ2AlphaR_of (thm4RBelow₂₇ n hA hP) (hP.twin rfl)
    Q3.TL4.omegaAutOddFreeR_proved Q3.TL4.lieKindZ2Model_proved

theorem WiredInputs₄₀.linkZ2L2
    (h : WiredInputs₄₀) (n : ℕ) :
    Q3.TL4.PlusLeaf Q3.TL4.TightLinkZ2L2R n := fun hA hP =>
  Q3.TL4.tightLinkZ2L2R_of (linkZ2Alpha₄₀ n hA hP)
    (Q3.TL4.tightLinkZ2L2BigR_of (thm4RBelow₂₇ n hA hP) hP.thm5 (hP.twin rfl)
      Q3.TL4.e4AutOddFreeR_proved Q3.TL4.omegaAutOddFreeR_proved (h.linkZ2L2Outer n hA hP)
      (h.linkZ2L2Inner n hA hP))

theorem WiredInputs₄₀.linkDiscNoTri
    (h : WiredInputs₄₀) (n : ℕ) :
    Q3.TL4.PlusLeaf Q3.TL4.LinkDisc.TightLinkDiscNoTriR n := fun hA hP =>
  Q3.TL4.LinkDisc.tightLinkDiscNoTriR_of (Q3.TL4.LinkDisc.tightLinkEdgeNoTriR_of
    (Q3.TL4.LinkDisc.tightLinkEdgeOddR_of (thm4RBelow₂₇ n hA hP) hP.thm5 (hP.twin rfl)
      Q3.TL4.e4AutOddFreeR_proved Q3.TL4.omegaAutOddFreeR_proved (h.linkEdgeOdd n hA hP)))

theorem WiredInputs₄₀.linkStarEdge
    (h : WiredInputs₄₀) (n : ℕ) :
    Q3.TL4.PlusLeaf Q3.TL4.TightLinkStarEdgeR n := fun hA hP =>
  Q3.TL4.tightLinkStarEdgeR_of (linkZ2Alpha₄₀ n hA hP) (h.linkZ2L2 n hA hP)
    (Q3.TL4.secIdE3MuZ2_of CFSG.Goldschmidt75.goldschmidtB3 Q3.TL4.muZ2Table_proved)
    Q3.TL4.muZ2Table_proved Q3.TL4.secIdStarNbrId3_proved Q3.TL4.secIdE4DStar_proved
    Q3.TL4.secIdE4O8TwoNbrs_proved Q3.TL4.lieKindTwoNbrs_proved Q3.TL4.lieKindE4Edge_proved
    Q3.TL4.model117_proved Q3.TL4.model117Pair_proved (Q3.TL4.tightAE286ExistR_three n)
    (Q3.TL4.tightAE286NoneR_three n) hA hP

theorem WiredInputs₄₀.linkCases
    (h : WiredInputs₄₀) (n : ℕ) :
    Q3.TL4.PlusLeaf Q3.TL4.TightLinkCasesR n := fun hA hP =>
  Q3.TL4.tightLinkCasesR_of (Q3.TL4.tightLinkTransR_three n)
    (Q3.TL4.LinkDisc.tightLinkDiscR_of (h.linkDiscNoTri n hA hP))
    (Q3.TL4.tightLinkDatumR_three n) (Q3.TL4.LinkE2.tightLinkE2R_plus n hA hP)
    (Q3.TL4.tightLinkExitR_of (h.linkStarEdge n hA hP))
    (Q3.TL4.tightLinkE4R_of Q3.TL4.secIdE4DStar_proved Q3.TL4.secIdE4O8TwoNbrs_proved)
    (Q3.TL4.tightLinkLieR_three_of_star (h.linkStarEdge n hA hP)) (thm4RBelow₂₇ n hA hP) hA hP

theorem star289Gen₄₀
    (hGH : GH74SectionalModels) : ∀ n, Q3.TL4.TightStar289GenR 3 n := fun _ =>
  Q3.TL4.S289G.tightStar289GenR_of Q3.TL4.secIdStarNbrId3_proved
    Q3.TL4.S289G.secIdStarGenS4_proved fun _ _ _ _ _ _ hL => thm6RBelow_of_large₃₃ hGH hL

theorem WiredInputs₄₀.alphaNoNbr
    (h : WiredInputs₄₀) (gp : CITPowBelow3) (n : ℕ) :
    Q3.TL4.PlusLeaf Q3.TL4.TightAlphaNoNbrR n := fun hA hP =>
  Q3.TL4.tightAlphaNoNbrR_three_of (h.linkCases n hA hP) (thm4RBelow₂₇ n hA hP)
    (hP.twin rfl) Q3.TL4.omegaAutOddFreeR_proved Q3.TL4.secIdStarNbrId3_proved
    Q3.TL4.secIdStarOrbId3_proved (star289ZFree₃₃ h.gh74 Q3.TL4.secIdE3S3NoTwist_proved n)
    (star289TFree₃₆ h.gh74 n) (star289Gen₄₀ h.gh74 n) (tightE4VtxSR_of_pow gp n)
    Q3.TL4.tightE4FrameR_three Q3.TL4.tightE4GenR_three Q3.TL4.model117_proved
    Q3.TL4.model117Pair_proved (Q3.TL4.tightAE286ExistR_three n)
    (Q3.TL4.tightAE286NoneR_three n) Q3.TL4.tightAECommonNbrR_holds

theorem WiredInputs₄₀.alpha
    (h : WiredInputs₄₀) (gp : CITPowBelow3) :
    ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightAlphaLeafR n := fun n hA hP =>
  Q3.TL4.tightAlphaLeafR3_of_linkGen (thm4RBelow₂₇ n hA hP) hP.thm5 (hP.twin rfl).toSet
    (secLinkGen₂₇ n hA hP) (h.alphaNoNbr gp n hA hP)

theorem WiredInputs₄₀.thm5
    (h : WiredInputs₄₀) (gp : CITPowBelow3) :
    ∀ n, Q3.TL4.Thm5StepR 3 n := fun n =>
  Q3.TL4.thm5StepR_three_of h.gh74 Q3.TL4.Small.leaf_l3Ne3 Q3.TL4.Small.leaf_u3Ne3
    (h.alpha gp n) (connR'₄₀ n)

theorem WiredInputs₄₀.e3E4O
    (h : WiredInputs₄₀) (n : ℕ) (hP : Q3.TL4.TightBelowRPlus 3 n) :
    Q3.TL4.TightE3E4O n :=
  Q3.TL4.tightE3E4O_of (Q3.PhilipHall.Frame.Twin1711.fin1711Sandwich_of_tables h.pfTables)
    (Q3.PhilipHall.Frame.Twin1711.fin1711Pairing_of_tables h.pfTables)
    (Q3.TL4.tightE3E4Sec_of Q3.TL4.tightE4Perfect_proved Q3.TL4.tightE3E4Good_proved
      Q3.TL4.secIdE4Edge_proved) hP

theorem WiredInputs₄₀.c17_11
    (h : WiredInputs₄₀) (n : ℕ) : Q3.TL4.TightC17_11R n := by
  intro Y _ _ R S t J u hF
  exact Q3.TL4.tightC17_11R_of (h.e3E4O n hF.plus) Y R S t J u
    hF

theorem WiredInputs₄₀.c17_11'
    (h : WiredInputs₄₀) (n : ℕ) : Q3.TL4.TightC17_11'R n := by
  intro Y _ _ R S t J u hF
  exact Q3.TL4.tightC17_11'R_of (h.e3E4O n hF.plus) Y R S t J
    u hF

theorem WiredInputs₄₀.e3E4
    (h : WiredInputs₄₀) (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightE3E4R n :=
  fun _ hP => Q3.TL4.tightE3E4Step_of_F (Q3.TL4.tightE3E4F_of_leaves (h.c17_11 n) (h.c17_11' n))
    hP

theorem c264Omega₄₀
    : ∀ n, Q3.TL4.TightC264Omega n := fun n hP Y _ _ Rd Sd z J S R T W t hs =>
  Q3.TL4.tightC264Omega_of (thm4RBelow₂₇ n hs.large.below hP) (lambdaComm₃₁ n hs.large.below hP)
    Q3.TL4.model264Rank3_proved Q3.TL4.model1521Twin3_proved
    (Q3.TL4.tightC263E4_of (thm4RBelow₂₇ n hs.large.below hP)
      (lambdaComm₃₁ n hs.large.below hP)) hP Y Rd Sd z J S R T W t hs

theorem e3Z2₄₀
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightE3Z2R n := fun hA hP =>
  Q3.TL4.tightE3Z2Step_of_F (Q3.TL4.tightE3Z2F_of_leaves'' (thm4RBelow₂₇ n hA hP)
    (fun hP' => s26Dich₂₇ n hA hP')
    (fun hP' => Q3.TL4.tightC26_4RG_of hP' (thm4RBelow₂₇ n hA hP') (hP'.twin rfl).toSet
      Q3.TL4.tightC264Pair_proved
      (Q3.TL4.tightC264E2_of (thm4RBelow₂₇ n hA hP')
        (Q3.TL4.tightLambdaCommR_three_of_plus hP' hA (thm4RBelow₂₇ n hA hP')
          Q3.TL4.secIdE4OddCent_proved))
      (Q3.TL4.tightC264NoTwinE4_of (thm4RBelow₂₇ n hA hP')) (c264Omega₄₀ n))
    (Q3.TL4.tightE3Z2Sec163_of Q3.TL4.muZ2Table_proved
      (Q3.TL4.secIdE3MuZ2_of CFSG.Goldschmidt75.goldschmidtB3 Q3.TL4.muZ2Table_proved)
      Q3.TL4.secIdE4Edge_proved)
    (Q3.TL4.tightE3C269S_of_gen (Q3.TL4.tightE3C269Gen_of Q3.TL4.muZ2Table_proved
      (Q3.TL4.secIdE3MuZ2_of CFSG.Goldschmidt75.goldschmidtB3 Q3.TL4.muZ2Table_proved)
      Q3.TL4.secIdE4Edge_proved Q3.TL4.e3C269L2_proved)) (Q3.TL4.tightE3Z2Fin_proved n)) hP

theorem WiredInputs₄₀.e3S3
    (h : WiredInputs₄₀) (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightE3S3R n :=
  fun hA hP => Q3.TL4.tightE3S3Step_of_F (Q3.TL4.tightE3S3F_of_leaves (thm4RBelow₂₇ n hA hP)
    Q3.TL4.tightE3S3Pick_proved
    (Q3.TL4.tightE3S3Sec163_of_center (Q3.TL4.tightE3S3Sec163Z_proved n))
    (Q3.TL4.tightE3S3Cent_of_notBeta (Q3.TL4.tightE3S3NotBeta_of_facts Q3.TL4.e3C269L2_proved
      Q3.TL4.e3S3GenL3_proved Q3.TL4.e3S3GenU3_proved Q3.TL4.e3S3GenM12_proved))
    (Q3.TL4.tightE3S3Orbit_of' (thm4RBelow₂₇ n hA hP))
    (Q3.TL4.tightE3S3Orth_of (thm4RBelow₂₇ n hA hP) h.model1524Om
      Q3.TL4.E3S3O.model1524Twin3E4_proved (Q3.TL4.tightE3S3Orbit_of' (thm4RBelow₂₇ n hA hP)))
    (Q3.TL4.tightE3S3Fin_proved n)) hP

theorem WiredInputs₄₀.steps
    (h : WiredInputs₄₀) (gp : CITPowBelow3) (n : ℕ) :
    Q3.TL4.TightPlusStep 3 n :=
  Q3.TL4.tightPlusStep_of_parts'
    (Q3.TA3.tightSmallBase_of_twin h.gh74 Q3.TA3.twin2M12Leaf_holds Q3.TA3.twin2Sz8Leaf_holds
      Q3.TA3.twin2AnLeaf_holds)
    (Q3.tightLargeEdgeS_holds n)
    (Q3.TL4.oddLeafStep_of_E3 (h.alpha gp n) (connR'₄₀ n)
      (Q3.TL4.e3LeafR'_of_parts (e3Z2₄₀ n) (h.e3S3 n) (h.e3E4 n)) (thm4RBelow₂₇ n))
    (Q3.TL4.connLeafStep_of_R' (connR'₄₀ n))
    (Q3.TL4.e3LeafStep_of_R' (h.alpha gp n)
      (Q3.TL4.e3LeafR'_of_parts (e3Z2₄₀ n) (h.e3S3 n) (h.e3E4 n)))
    (thm4RBelow₂₇ n)
    (Q3.TC.Thin.thmD2Step_of_leaves₂
      (Q3.TC.Thin.dLeafC_of₂ (Q3.TC.Thin.d1GenLeaf_holds 3) h.cLeafE8 h.cLeafE64 h.cLeafE29
        h.cLeafAE) h.dLeafE4 h.dLeafStar h.dLeafEnd n)
    (Q3.TL4.thmD1StepR_of_core (Q3.TL4.d1Core3 (n + 1))) (Q3.TL4.thm6StepR_three h.gh74 n)
    (h.thm5 gp n) (h.twin n)

theorem WiredInputs₄₀.toWired₂₀
    (h : WiredInputs₄₀) (gp : CITPowBelow3) : WiredInputs₂₀ where
  gh74 := h.gh74
  twistAllTwin := fun n hA => Q3.TL4.tightTwistAllTwin_at
    ((Q3.TL4.tightBelowRPlus_of_step (h.steps gp) n hA).twin rfl) hA
  frameAEmptyP := h.frameAEmptyP
  benderEnd := Q3.TL4.tightBenderEndR
  dLeafC := Q3.TC.Thin.dLeafC_of₂ (Q3.TC.Thin.d1GenLeaf_holds 3) h.cLeafE8 h.cLeafE64 h.cLeafE29
    h.cLeafAE
  dLeafE4 := h.dLeafE4
  dLeafStar := h.dLeafStar
  dLeafEnd := h.dLeafEnd
  d1Core := fun n => Q3.TL4.d1Core3 n
  thm4 := thm4RBelow₂₇
  thm6 := Q3.TL4.thm6StepR_three h.gh74
  thm5 := h.thm5 gp
  twin := h.twin
  clique5 := clique5₄₀
  triangle := triangle₄₀
  alpha := h.alpha gp
  hyp51 := hyp51₄₀
  s26Dich := s26Dich₂₇
  c26_13 := c26_13₄₀
  e4SecGen := e4SecGen₂₇
  lambdaComm := lambdaComm₃₁
  alphaFrame := alphaFrame₂₇
  secNoRoot := secNoRoot₂₇
  e3Z2 := e3Z2₄₀
  e3S3 := h.e3S3
  e3E4 := h.e3E4

theorem memberFreeSocle_of_wired₄₀
    (h : WiredInputs₄₀) (gp : CITPowBelow3) :
    Q3.Q3T.MemberFreeSocleOuter3 :=
  memberFreeSocle_of_wired₁₆ (h.toWired₂₀ gp).toWired₁₉.toWired₁₈.toWired₁₇.toWired₁₆

theorem milestone_of_wired₄₀
    (h : WiredInputs₄₀)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hJ : Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)))
    (hzJ : z ∈ J) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Assembly.ComponentType.OddLieType G ∨ Nonempty (G ≃* Assembly.ComponentType.M11) :=
  have gp : CITPowBelow3 := citPowBelow3_of_gh74_memberFreeP h.gh74 fun gp =>
    memberFreeSocle_of_wired₄₀ h gp
  milestone_of_wired₂₀ (h.toWired₂₀ gp) G hnonab z hz J hJ hzJ S hS

end Wired

end CFSG.ComponentClassification.QuaternionComponent
