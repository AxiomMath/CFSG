module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsFusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsLemma42
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsCase2
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsLemma43
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsLemma44
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsLemma45
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC GenericComponentClass)

variable {G : Type} [Group G] [Finite G]

theorem tits_false (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hK : TypeIIKFacts)
    (hClass : GenericComponentClass G) (hA10 : A10Facts) (hMcL : ExtraFacts IsMcLType 5 McLShape)
    (hJ4 : ExtraFacts IsJ4Type 11 J4Shape) (hSz : Sz32Facts) (hSz' : Sz32OpenFacts)
    (hdata : Sz32DataFacts) {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}
    (hX : TitsFacts) (hc : PointConfig IsTitsType G 5 P M x J) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨U, hU⟩ := plane_exists_iiplane hX.sylow hX.noOuter hc
  have hfus := tits_fusion_core hS hD1 hU0 hK.sig hX hc
  have hL42 := tits_lemma42 hS hD1 hU0 hClass hX hA10 hMcL hJ4 hSz hSz' hdata hc hfus hU
  have hnorm := tits_normal_core hS hD1 hU0 hK.inner hK.weak hX hc hfus
  have hL43 := tits_lemma43 hS hD1 hU0 hX hc hnorm hU
  have hL44 := tits_cor47 hS hD1 hU0 hX hc
  have hL45 := tits_lemma45_G hS hD1 hU0 hX hc hU
  have hF := plane_hF hS hX.sylow hX.noOuter hc hfus hU
  have hUP : U ≤ (P : Subgroup G) := hU.le.trans inf_le_left
  exact typeII_endgame41 hS hU0 hD1 hK.inner hK.weak hc.sigma hc.five hc.core hc.generic.1
    hc.generic.2.1.2.1 hc.generic.2.1.2.2.1 hU.elem hU.card hUP hU.mem hF hL42 hL43 hL45 hL44

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
