module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWrap
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointX
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointTypes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC GenericComponentClass)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem tits_lemma42 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hClass : GenericComponentClass G) (hX : TitsFacts) (hA10 : A10Facts)
    (hMcL : ExtraFacts IsMcLType 5 McLShape) (hJ4 : ExtraFacts IsJ4Type 11 J4Shape)
    (hSz : Sz32Facts) (hSz' : Sz32OpenFacts) (hdata : Sz32DataFacts)
    (hc : PointConfig IsTitsType G 5 P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G))
    {U : Subgroup G} (hU : IIPlane 5 P x J U) :
    ∀ a ∈ U, a ∉ Subgroup.zpowers x → Subgroup.centralizer ({a} : Set G) ≤ M := by
  intro a ha hax
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hTcard, hTel, -⟩ := plane_T_structure hX.sylow hc
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩ := plane_S_decomp hX.sylow hX.noOuter hc
  have hSP : u3S P x = (P : Subgroup G) := inf_eq_left.2 hfus.1
  exact lemma42_routeW hS hU0 hD1 hClass (by norm_num) hc.sigma hc.core hc.fail hc.larger
    hc.generic.2.1.2.1 hc.generic.2.1.2.2.1 hfus.1 hfus.2
    (plane_x_not_mem_commutator hX.sylow hX.noOuter hc hfus.1)
    (fun y hy _ => plane_three_le_pRank_centralizer hX.sylow hX.noOuter hc hfus.1 hy)
    (fun Q _ _ hQ hz => secondPointFacts_of_class (by norm_num) hQ hz hX hA10 hMcL hJ4)
    (fun _ => sz32_second_point_false hS hU0 hD1 hSz hSz' hdata hc.core hc.sigma
      hc.generic.2.1.2.2.1 hc.generic.2.1.2.1 hfus.1 (hsup.trans hSP) hZT hTZ hTel.2 hZcyc hxZ)
    a ((hU.le ha).1) (hU.elem.2 a ha) hax

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
