module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayHolds
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRoot

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

theorem hStray_twoSec_holds
    {G : Type} [Group G] [Finite G] {x : G} {t : TwoSec x}
    {Sg V : Subgroup (TwoSec x)} (h : SwapShape t Sg V) :
    ∀ J : Subgroup (TwoSec x), CFSG.IsComponent J →
      ⁅(⁅Sg, Sg⁆ : Subgroup (TwoSec x)), J⁆ = ⊥ → t ∈ J :=
  hStray_of_swapShape_holds h

end CFSG.OddStandard.AltStdSec.SwapPartner
