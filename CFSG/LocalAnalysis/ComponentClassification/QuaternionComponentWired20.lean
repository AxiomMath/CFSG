module

public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired19
public import CFSG.ClassicalInvolution.Q3.TL4StepAsm
public import CFSG.ClassicalInvolution.Q3.TL4StepRed
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetBridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetCore
public import CFSG.ClassicalInvolution.Q3.TL3T25
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf1
public import CFSG.ClassicalInvolution.MilestoneAssemblyWired15
public import CFSG.ClassicalInvolution.Q3.TL4D4NCCor
public import CFSG.ClassicalInvolution.Q3.TL4OddFrNon
public import CFSG.ClassicalInvolution.Q3.TL4OddSecEdge
public import CFSG.ClassicalInvolution.Q3.TL4Sep2FB
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Q
public import CFSG.GH74.GLS.C3.Layer2.L5C19
public import CFSG.GH74.GLS.C3.Layer2.L5C5c
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Kill
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.GH74.Generic.S1.Exo.NbDefs
public import CFSG.GH74.Generic.S45.LEvSporGen
public import CFSG.GH74.KGroups.L28Tables
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1ToralData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternal
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitCase
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Sporadic.Co1.Module.TwoBCertBase
public import CFSG.Sporadic.HeldB.OuterFixed
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import Certificates.Certificate10025
public import Certificates.Certificate8026Base

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly

set_option linter.unusedSectionVars false

structure WiredInputs₂₀ : Prop where
  gh74 : GH74SectionalModels
  twistAllTwin : ∀ n, Q3.TightTwistAllTwin n
  frameAEmptyP : Q3.PhilipHall.Frame.FrameAEmptyPf.FrameAEmptyP
  benderEnd : Q3.TL4.TightBenderEndR
  dLeafC : Q3.TC.Thin.DLeafC 3 (Q3.TC.Thin.PackIH 3)
  dLeafE4 : Q3.TC.Thin.DLeafE4 3 (Q3.TC.Thin.PackIH 3)
  dLeafStar : Q3.TC.Thin.DLeafStar 3 (Q3.TC.Thin.PackIH 3)
  dLeafEnd : Q3.TC.Thin.DLeafEnd 3 (Q3.TC.Thin.PackIH 3)
  d1Core : ∀ n, Q3.TL4.D1Core3 n
  thm4 : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.Thm4RBelow n
  thm6 : ∀ n, Q3.TL4.Thm6StepR 3 n
  thm5 : ∀ n, Q3.TL4.Thm5StepR 3 n
  twin : ∀ n, Q3.TL4.TwinStepR 3 n
  clique5 : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightSec5CliqueR n
  triangle : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightSecTriangleR n
  alpha : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightAlphaLeafR n
  hyp51 : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightHyp51TriR n
  s26Dich : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightS26DichR n
  c26_13 : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightC26_13R n
  e4SecGen : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightE4SecGenR n
  lambdaComm : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightLambdaCommR n
  alphaFrame : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightAlphaFrameR n
  secNoRoot : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightSecNoRootR n
  e3Z2 : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightE3Z2R n
  e3S3 : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightE3S3R n
  e3E4 : ∀ n, Q3.TL4.PlusLeaf Q3.TL4.TightE3E4R n

section Wired


theorem WiredInputs₂₀.smallBase
    (h : WiredInputs₂₀) : Q3.TightSmallBase :=
  Q3.TA3.tightSmallBase_of_twin h.gh74 Q3.TA3.twin2M12Leaf_holds Q3.TA3.twin2Sz8Leaf_holds
    Q3.TA3.twin2AnLeaf_holds

theorem WiredInputs₂₀.connR'
    (h : WiredInputs₂₀) (n : ℕ) :
    Q3.TL4.PlusLeaf Q3.TL4.TightConnLeafR' n :=
  Q3.TL4.connLeafR'_of_residuals₇ (h.s26Dich n) (h.c26_13 n) (h.clique5 n) h.benderEnd
    (h.e4SecGen n) (h.lambdaComm n) (h.triangle n) (h.thm4 n) (h.hyp51 n) (h.alphaFrame n)
    (h.secNoRoot n)

theorem WiredInputs₂₀.e3R'
    (h : WiredInputs₂₀) (n : ℕ) :
    Q3.TL4.PlusLeaf Q3.TL4.TightE3LeafR' n :=
  Q3.TL4.e3LeafR'_of_parts (h.e3Z2 n) (h.e3S3 n) (h.e3E4 n)

theorem WiredInputs₂₀.oddStep
    (h : WiredInputs₂₀) (n : ℕ) : Q3.TL4.OddLeafStep n :=
  Q3.TL4.oddLeafStep_of_E3 (h.alpha n) (h.connR' n) (h.e3R' n) (h.thm4 n)

theorem WiredInputs₂₀.steps
    (h : WiredInputs₂₀) (n : ℕ) : Q3.TL4.TightPlusStep 3 n :=
  Q3.TL4.tightPlusStep_of_parts (h.twistAllTwin n) h.smallBase (Q3.tightLargeEdgeS_holds n)
    (h.oddStep n) (Q3.TL4.connLeafStep_of_R' (h.connR' n))
    (Q3.TL4.e3LeafStep_of_R' (h.alpha n) (h.e3R' n)) (h.thm4 n)
    (Q3.TC.Thin.thmD2Step_of_leaves₂ h.dLeafC h.dLeafE4 h.dLeafStar h.dLeafEnd n)
    (Q3.TL4.thmD1StepR_of_core (h.d1Core (n + 1))) (h.thm6 n) (h.thm5 n) (h.twin n)

theorem WiredInputs₂₀.largeLiftS
    (h : WiredInputs₂₀) (n : ℕ) : Q3.TightLargeLiftS n :=
  fun hA => Q3.TL4.tightLargeLiftS_of_steps (h.oddStep n) (Q3.TL4.connLeafStep_of_R' (h.connR' n))
    (Q3.TL4.e3LeafStep_of_R' (h.alpha n) (h.e3R' n)) (h.thm4 n) hA
    (Q3.TL4.tightBelowRPlus_of_step h.steps n hA) hA

theorem WiredInputs₂₀.centTwin
    (h : WiredInputs₂₀) (n : ℕ) : Q3.TightCentTwinLift n :=
  fun hA => Q3.TL4.tightCentTwinLift_at ((Q3.TL4.tightBelowRPlus_of_step h.steps n hA).twin rfl) hA

theorem WiredInputs₂₀.toWired₁₉
    (h : WiredInputs₂₀) : WiredInputs₁₉ where
  gh74 := h.gh74
  twistAllTwin := h.twistAllTwin
  largeLiftS := h.largeLiftS
  centTwin := h.centTwin
  frameLarge := Q3.PhilipHall.Frame.residualCFrameLarge_of_twinLiftSet
    (fun n hA hB => (Q3.TL4.twinLift_of_steps h.steps n hA hB).toSet)
    (Q3.PhilipHall.Frame.FrameAEmptyPf.frameAEmpty_of_frameAEmptyP h.frameAEmptyP
      (Q3.TL4.tightBelowRPlus_of_step h.steps)) h.twistAllTwin h.smallBase h.largeLiftS

theorem milestone_of_wired₂₀
    (h : WiredInputs₂₀)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hJ : Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)))
    (hzJ : z ∈ J) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Assembly.ComponentType.OddLieType G ∨ Nonempty (G ≃* Assembly.ComponentType.M11) :=
  milestone_of_wired₁₉ h.toWired₁₉ G hnonab z hz J hJ hzJ S hS

end Wired

end CFSG.ComponentClassification.QuaternionComponent
