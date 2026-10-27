module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGMain
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.ZJGe
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGStep1
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGStep4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGZJ

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section Inputs

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem stepKGroupCore_of_steps (hKF : KFact64iiL) (hL613b : KGL613b) (hAutO : KFactAutAltOrder)
    (hAutE : KFactAutAltEmbed) (h2024 : KG2024) (h2401 : KFact2401Three) (hAlt6 : KGAltSix)
    (h56 : KGSteps56) : StepKGroupCore := by
  intro G _ _ p P M x z hS hx hz H S hopt hO hΩ hnpc h2
  obtain ⟨L, d3⟩ := KGC.exists_kgData3 hKF hS hx hz hopt hO hΩ hnpc h2
  haveI : ((GLBPrimeCore p H).subgroupOf H).Normal := d3.toData.normal_subgroupOf
  have hG := KGC.kgStrongEmb_of_L613b hL613b hS hx hz hnpc
  have hchev := d3.chev_or_alt kFactZJFactorizationGe_holds
  have h4 := KGQ.kgroup_step4 d3.toData.cfg (d3.toData.strong_img hG) hAutO hAutE h2024 h2401
    hAlt6 hchev
  exact h56 G p P M x z hS hx hz H S hopt hO hΩ hnpc h2 L d3 hG h4

theorem stepKGroupCore_of_inputs (hKF : KFact64iiL) (hL613b : KGL613b)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (hAlt6 : KGAltSix) (h2715 : KFact2715) (h131 : KFact131)
    (hpc : KFactParabolicCover) (h5s : KGStep5Sylow) (h6n : KGStep6Noncyc) (h6c : KGStep6Cyc) :
    StepKGroupCore :=
  stepKGroupCore_of_steps hKF hL613b hAutO hAutE h2024 h2401 hAlt6
    (kgSteps56_of_inputs h2715 h131 hpc h5s h6n h6c)

end Inputs

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
