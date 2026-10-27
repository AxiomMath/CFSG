module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.NotStandard
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.E3

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem m22_inner_false
    (hSol : CFSG.EvenSporadicStandard.Fin76b.SolomonZ2A6)
    (h : StdHyp G L) (hL : IsSporadic L .M22) {z : G} (hz : z ∈ centralizer (L : Set G))
    (hz2 : orderOf z = 2) (hC : centralizer ({z} : Set G) ≤ L ⊔ zpowers z) : False :=
  m22_inner_false_of_inputs hSol fin76aWreathNoFusionM22 h hL hz hz2 hC

end CFSG.EvenSporadicStandard.M22Std
