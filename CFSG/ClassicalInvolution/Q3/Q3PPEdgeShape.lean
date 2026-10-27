module

public import CFSG.ClassicalInvolution.Q3.Q3PPBal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Q3.Q3OF
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3W

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

namespace EdgeData

theorem alphaCore_edge_eq_bot_of_oddCoreIn_layer_eq_bot (hR : RouteD3Setup K z)
    (h : EdgeData K K₁ K₂ z₁ z₂)
    (hO : oddCoreIn (centralizingLayer (conjClass3 K) {z₁ * z₂}) = ⊥) :
    alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ := by
  refine (alphaCore_pair_eq_bot_iff_layer hR h.mem₁ h.mem₂ h.cls₁ h.cls₂ h.ne
    h.le_centralizer₁).mpr fun q hq => ?_
  rw [hO, Subgroup.mem_bot] at hq
  subst hq
  simp

end EdgeData

end Edge

end CFSG.ClassicalInvolution.Q3.Q3PP
