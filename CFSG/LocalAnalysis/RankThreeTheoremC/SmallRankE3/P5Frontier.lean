module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5LargeSteps
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5IiiFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1RedMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

section Frontier

theorem gl83SmallRankLemma630E3_of_open'
    (h3 : SlotP614Three) (hL : SlotP614LargeD2)
    (h5 : SlotLemma630FiveCond) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
      GL83SmallRankLemma630Res G :=
  fun G _ _ hS hD1 hD2 hU0 => lemma630Res_of_five_of_d1 hS hD1
    (KFactProofs.RankTwoUniq.kFactRankTwoUniqueness_of_core KFactProofs.RankTwoUniq.k1Core_holds) kfactRankThreeStructure_proved
    (gl83SmallRankLemma62At3_proved G) kFactOutQ8Quaternion_holds (h3 G hS hD1)
    (h5 G hS hD1 (fun P M x z T hf S₀ hS₀ hS₀1 hzS₀ =>
      hL G hS hD1 hD2 hU0 5 (by norm_num) P M x z T hf S₀ hS₀ hS₀1 hzS₀))

theorem gl83SmallRankInterfaceE3_of_open'
    (h3 : SlotP614Three) (hL : SlotP614LargeD2)
    (h5 : SlotFitting628Five) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
      GL83SmallRankInterfaceW G := by
  intro G _ _ hS hD1 hD2 hU0
  refine interfaceW_of_five_of_d1 hS hD1 (KFactProofs.RankTwoUniq.kFactRankTwoUniqueness_of_core
      KFactProofs.RankTwoUniq.k1Core_holds)
    kfactRankThreeStructure_proved (gl83SmallRankLemma62At3_proved G) ?_ (h5 G hS hD1)
  intro p P M x z T hf
  by_cases hp : p = 3
  · subst hp
    exact h3 G hS hD1 P M x z T hf
  · exact hL G hS hD1 hD2 hU0 p hp P M x z T hf

end Frontier

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
