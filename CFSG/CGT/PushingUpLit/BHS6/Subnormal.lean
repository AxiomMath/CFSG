module

public import CFSG.Assembly.Subnormal
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.CGT.PushingUpLit.BHS6

variable {Γ : Type*} [Group Γ]

theorem isSubnormal_subgroupOf_of_open {X K : Subgroup Γ} (h : CFSG.Open.IsSubnormal K X) :
    (K.subgroupOf X).IsSubnormal :=
  CFSG.Open.IsSubnormal.subgroupOf h

theorem open_isSubnormal_top_of_isSubnormal {H : Subgroup Γ} (h : H.IsSubnormal) :
    CFSG.Open.IsSubnormal H ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib h

end CFSG.CGT.PushingUpLit.BHS6
