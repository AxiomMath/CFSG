module

public import CFSG.LocalAnalysis.RankThreeUC.CoreWitness
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.GNSettingM
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G]

theorem gnSetting_M (hS : Standing G) (hUC : rankThreeUC G) (hX : D1NoXBlock3 G)
    {M T : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : GNSetting ↥M (T.subgroupOf M) := by
  have := hS.simple
  have hMtop : M ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hM.1
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.gnSetting_of_subgroup hS.kProper hMtop
    (hS.charTwo M hM.1) (CFSG.ABGLocalTools.isSylowOf_iff.mp hT)
    (fun Y hYM hYs hY => hX (setting_of_rankThreeUC hS hUC) M Y hM hYM hYs hY)

end CFSG.LocalAnalysis.RankThreeUC.S15
