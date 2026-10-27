module

public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Glue

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic.BProg.B3.FalseCtxS45

theorem rank_of_xbar_not_mem {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G}
    {D J : Subgroup G} (hc : Ctx21 G x K A a D J) (h : L5U5.xbar a ∉ PumpCalc.bar a J) :
    SectionalTwoRankLE (↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J)) 3 := by
  have hRC := not_rankCertified_three_of_xbar_not_mem hc.hyp.gen4 hc.obs.y_ord h
  have h1 : SectionalTwoRankLE ↥(PumpCalc.bar a J) 3 := by
    by_contra h2
    exact hRC (rankCertified_of_not_sectionalTwoRankLE h2)
  exact SectionalTwoRankLE.quotient _ h1

end CFSG.GH74.Generic.BProg.B3
