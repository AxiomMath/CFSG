module

public import CFSG.GH74.Generic.S3.LeavesR
public import CFSG.GH74.Generic.S3.PumpLift
public import CFSG.GH74.Generic.S3.PumpDiag
public import CFSG.GH74.Generic.Lifting
public import CFSG.GH74.GLS.TwoThin.Pumpup
public import CFSG.GH74.GLS.TwoThin.PumpData
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.S3.J2Star
public import CFSG.GH74.Generic.JMaxDefs
public import CFSG.GH74.Generic.S3.OnlyInvT4
public import CFSG.GH74.Generic.S3.LxySplit
public import CFSG.GH74.Generic.S3.LyVert
public import CFSG.GH74.Generic.S3.OnlyInvT3
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.E2
  CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem Gen4Comp.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : Gen4Comp X) :
    Gen4Comp Y := by
  refine ⟨Gen4.of_mulEquiv e h.1, ?_⟩
  rcases h.2 with h3 | hc
  · exact Or.inl (SectionalTwoRankLE.of_mulEquiv e h3)
  · right
    intro hbot
    apply hc
    have := Subgroup.map_center_eq e
    rw [hbot] at this
    exact (Subgroup.map_eq_bot_iff_of_injective (center X) e.injective).1 this

end CFSG.GH74.Generic.S3
