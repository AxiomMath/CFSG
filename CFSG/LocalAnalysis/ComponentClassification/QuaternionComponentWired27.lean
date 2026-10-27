module

public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired25
public import CFSG.ClassicalInvolution.Q3.TL4E3C17
public import CFSG.ClassicalInvolution.Q3.TL4E3E4O
public import CFSG.ClassicalInvolution.Q3.TL4E3E4Sec
public import CFSG.ClassicalInvolution.Q3.TL4E3E4PerfD
public import CFSG.ClassicalInvolution.Q3.TL4E3E4Good
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfTables
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoMain
public import CFSG.ClassicalInvolution.Q3.TL4GLinkAlpha
public import CFSG.ClassicalInvolution.Q3.TL4OddLieAll
public import CFSG.ClassicalInvolution.Q3.TL4LinkStarEdge
public import CFSG.ClassicalInvolution.Q3.TL4Mdl1643A
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2Defs
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GL
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.GH74.Generic.Context
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts28
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.ClassicalInvolution.Q3.TL4OddLieZ2
public import CFSG.ClassicalInvolution.Q3.TL4AE286Exist
public import CFSG.ClassicalInvolution.Q3.TL4AE286None
public import CFSG.ClassicalInvolution.Q3.TL4Conn264F
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GU
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.ClassicalInvolution.Balance.WeakFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpClass
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189b
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEApply
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf182
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf2Base
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3OddStand
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoE4O8A
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

section Wired

theorem thm4RBelow₂₇
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.Thm4RBelow n :=
  fun hA hP => Q3.TL4.thm4RBelow_of_cit3Below hA hP
    (Q3.TL4.exitModelR_of hA hP (Q3.TL4.exitTwoClassR_of hA hP))

theorem secLinkGen₂₇
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightSecLinkGenR n :=
  fun hA hP => Q3.TL4.tightSecLinkGenR_three_of_plus hA hP (thm4RBelow₂₇ n hA hP)
    Q3.TL4.secIdE2LinkGen_proved Q3.TL4.secIdE4LinkCent_proved

theorem s26Dich₂₇
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightS26DichR n :=
  fun hA hP => Q3.TL4.tightS26DichR_three_of_below (Q3.TL4.secIdentDatum3_of hP hA)
    (thm4RBelow₂₇ n hA hP) (Q3.TL4.secIdE2EdgelessBelow_of hP.thmD.d2)
    (Q3.TL4.secIdE4Edge_of_graphFacts e4QuatGraphFacts_of_exLie₂₅)
    (Q3.TL4.secIdLieEdgeless3Below_of ((Uniform.citBelowT_three_iff (by norm_num) n).mpr hA))
    (Q3.TL4.secIdE3MuZ2_of CFSG.Goldschmidt75.goldschmidtB3 Q3.TL4.muZ2Table_proved)
    Q3.TL4.muZ2Table_proved Q3.TL4.MF164.model164_proved

theorem e4SecGen₂₇
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightE4SecGenR n :=
  fun hA hP => Q3.TL4.tightE4SecGenR_three_of_below (Q3.TL4.secIdentDatum3_of hP hA)
    (thm4RBelow₂₇ n hA hP) ((Uniform.citBelowT_three_iff (by norm_num) n).mpr hA)
    (Q3.PhilipHall.InductionBridge.ih8T_of_cit3Below hA)
    (Q3.TL4.secIdE2DStarBelow_of hP.thmD.d2)
    (Q3.TL4.secIdE4DStar_of_graphFacts e4QuatGraphFacts_of_exLie₂₅) Q3.TL4.secIdE4GenAE5_proved

theorem secNoRoot₂₇
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightSecNoRootR n :=
  fun hA hP => Q3.TL4.tightSecNoRootR_three_of_below (Q3.TL4.secIdentDatum3_of hP hA)
    (thm4RBelow₂₇ n hA hP) ((Uniform.citBelowT_three_iff (by norm_num) n).mpr hA)
    (Q3.PhilipHall.InductionBridge.ih8T_of_cit3Below hA)
    (Q3.TL4.secIdE2DStarBelow_of hP.thmD.d2)
    (Q3.TL4.secIdE4DStar_of_graphFacts e4QuatGraphFacts_of_exLie₂₅) Q3.TL4.secIdNoRootAE5_proved

theorem alphaFrame₂₇
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightAlphaFrameR n :=
  fun hA hP => Q3.TL4.tightAlphaFrameR_of
    (Q3.TL4.tightHyp51TriR_three_of_components (thm4RBelow₂₇ n hA hP) hP.thm5 (hP.twin rfl).toSet)
    (thm4RBelow₂₇ n hA hP) (secLinkGen₂₇ n hA hP)

end Wired

end CFSG.ComponentClassification.QuaternionComponent
