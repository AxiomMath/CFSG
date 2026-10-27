module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Fusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43Asm
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFreeProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma44
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma45
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10HF
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC GenericComponentClass)

variable {G : Type} [Group G] [Finite G]

theorem a10_false (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hK : TypeIIKFacts)
    (hClass : GenericComponentClass G) (hTits : TitsFacts) (hMcL : ExtraFacts IsMcLType 5 McLShape)
    (hJ4 : ExtraFacts IsJ4Type 11 J4Shape) (hSz : Sz32Facts) (hSz' : Sz32OpenFacts)
    (hdata : Sz32DataFacts) (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hI : KFactI1434) (hU : KFactU44Data) {P : Sylow 5 G} {M : Subgroup G} {x : G}
    {J : Subgroup G} (hX : A10Facts) (hXe : A10Ext) (hc : PointConfig IsA10Type G 5 P M x J) :
    False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hB := a10_fusion_core hS hD1 hU0 hK.sig hX hXe hc ψ hψ hker hQ
  obtain ⟨U, hUP, hγ⟩ := a10_plane hX hXe hc ψ hψ hker hQ
  have hL42i := a10_lemma42_i ψ hB hUP hγ
  have hL42 := a10_lemma42 hS hD1 hU0 hClass hTits hX hMcL hJ4 hSz hSz' hdata hXe hc ψ hψ hker hQ hB
    hUP hγ
  have hL43 := a10_lemma43_asm hS hD1 hU0 hK.inner hK.weak hSch hI hU hX hXe a10_L43Facts_holds hc ψ
      hψ hker hQ hB hUP hγ
  have hL44 := a10_cor47 hS hD1 hU0 hX hc
  have hL45 := a10_lemma45_G hS hD1 hU0 hX hXe hc ψ hψ hker hQ hUP hγ
  have hF := a10_hF hS hX hc ψ hB hUP hL42i
  have hUS : U ≤ (P : Subgroup G) := hUP.le.trans inf_le_left
  exact typeII_endgame41 hS hU0 hD1 hK.inner hK.weak hc.sigma hc.five hc.core hc.generic.1
    hc.generic.2.1.2.1 hc.generic.2.1.2.2.1 hUP.elem hUP.card hUS hUP.mem hF hL42 hL43 hL45 hL44

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
