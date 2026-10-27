module

public import CFSG.GH74.GLS.Stage2.Local.Prop27W

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local.Prop28

theorem compsGood_of_leaf_prop27W
    (h27 : Leaf_Prop27W Stage2Ctx0) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx0 G z k S →
      k ≠ Kind.m12 → ∀ y : G, Prop27Y z y → CompsGood y := by
  intro G _ _ z k S hctx hk y hy
  rcases kind_cases_of_data hctx.central hctx.data with hone | ⟨hcls, x₀, -, -, hcl⟩
  · exact absurd (isCentralInvolution_of_isConj' hctx.central
      (hone z y hctx.central.1 hy.2.1.1)) hy.2.1.2
  · exact compsGood_of_prop27W (hcls.resolve_right hk) hctx.central hcl (h27 G z k S hctx) hy

end CFSG.GH74.GLS.Stage2.Local
