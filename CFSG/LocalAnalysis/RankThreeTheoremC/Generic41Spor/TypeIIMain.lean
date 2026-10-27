module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIFusionGen
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma42
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma44
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma43
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIHF
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma45
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC GenericComponentClass)

variable {G : Type} [Group G] [Finite G]

theorem j4_false (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hK : TypeIIKFacts)
    (hClass : GenericComponentClass G) (hTits : TitsFacts) (hA10 : A10Facts)
    (hMcL : ExtraFacts IsMcLType 5 McLShape) {P : Sylow 11 G} {M : Subgroup G} {x : G}
    {J : Subgroup G} (hX : ExtraFacts IsJ4Type 11 J4Shape) (hc : PointConfig IsJ4Type G 11 P M x J) :
    False := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hfus := typeII_fusion_core_of_se hS hD1 hU0 hK hX typeSE_j4 hc
  have hU := j4_plane hX hc
  have hL42 := j4_lemma42 hS hClass hD1 hU0 hTits hA10 hMcL hX hc hfus
  have hodd := typeII_cor47 hS hD1 hU0 hX
    (fun A B _ _ e h => ⟨h.1, h.2.map fun f => e.symm.trans f⟩) hc
  have hnorm := typeII_normal_core hS hD1 hU0 hK hX hc hfus
  have hL43 := j4_lemma43 hS hD1 hU0 hX hc hnorm
  have hL45 := j4_lemma45_G hS hD1 hU0 hX hc
  have hF := typeII_hF hS hX hc hfus hU
  have hUP : u3U0 P x J ≤ (P : Subgroup G) := hU.le.trans inf_le_left
  exact typeII_endgame41 hS hU0 hD1 hK.inner hK.weak hc.sigma hc.five hc.core hc.generic.1
    hc.generic.2.1.2.1 hc.generic.2.1.2.2.1 hU.elem hU.card hUP hU.mem hF hL42 hL43 hL45 hodd

theorem mcl_false (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hK : TypeIIKFacts)
    (hClass : GenericComponentClass G) (hTits : TitsFacts) (hA10 : A10Facts)
    (hJ4 : ExtraFacts IsJ4Type 11 J4Shape) (hSz : Sz32Facts) (hSz' : Sz32OpenFacts)
    (hdata : Sz32DataFacts) {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}
    (hX : ExtraFacts IsMcLType 5 McLShape) (hc : PointConfig IsMcLType G 5 P M x J) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfus := typeII_fusion_core_of_se hS hD1 hU0 hK hX typeSE_mcl hc
  obtain ⟨U, hU, hnc⟩ := mcl_plane hX hc
  have hL42 := mcl_lemma42 hS hClass hD1 hU0 hTits hA10 hJ4 hSz hSz' hdata hX hc hfus hU
  have hodd := typeII_cor47 hS hD1 hU0 hX
    (fun A B _ _ e h => ⟨h.1, h.2.map fun f => e.symm.trans f⟩) hc
  have hnorm := typeII_normal_core hS hD1 hU0 hK hX hc hfus
  have hL43 := mcl_lemma43 hS hD1 hU0 hX hc hnorm hU
  have hL45 := mcl_lemma45_G hS hD1 hU0 hX hc hU hnc
  have hF := typeII_hF hS hX hc hfus hU
  have hUP : U ≤ (P : Subgroup G) := hU.le.trans inf_le_left
  exact typeII_endgame41 hS hU0 hD1 hK.inner hK.weak hc.sigma hc.five hc.core hc.generic.1
    hc.generic.2.1.2.1 hc.generic.2.1.2.2.1 hU.elem hU.card hUP hU.mem hF hL42 hL43 hL45 hodd

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
