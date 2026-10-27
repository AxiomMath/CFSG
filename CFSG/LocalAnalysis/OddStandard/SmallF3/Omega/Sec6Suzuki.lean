module

public import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.GH74.GLS.C3.Layer1.St1RigTwoGrp

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec6_suzuki_four {G : Type} [Group G] [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    {y : G} (hyT : y ∈ T) (hy : orderOf y = 2)
    (hc : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = 4) : CFSG.Open.pRank 2 T ≤ 2 := by
  rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact CFSG.GH74.GLS.C3.Layer1.PumpRigid.pRank_le_two_of_centralizer_card_four hT hyT hy hc

end CFSG.OddStandard.SmallF3.Omega
