module

public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement

public section

namespace CFSG.GH74.KGroups.TwoM12

open Subgroup CFSG.Blueprint

theorem m12_cover_of_standard
    (K : Type) [Group K] [Finite K] (hq : CFSG.IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) (hM : NativeSporadic.IsSporadic (K ⧸ center K) .M12) :
    Nat.card (center K) ≤ 2 :=
  CFSG.ComponentClassification.StandardRecognition.m12J2CentralTwoGroupOrderBound K
    ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩ hZ (Or.inl hM)

end CFSG.GH74.KGroups.TwoM12
