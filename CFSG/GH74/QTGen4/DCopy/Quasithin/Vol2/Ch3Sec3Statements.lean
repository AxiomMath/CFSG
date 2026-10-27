module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch3Sec3Setup

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G]

@[expose] def Stmt3_3_14_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    mPlus L T = L ∧ M ≤ Subgroup.normalizer (L : Set G)

end CFSG.Quasithin.H13
