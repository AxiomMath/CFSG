module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Assembly
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95U4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95U5

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint

theorem ivk95Leaves_proved :
    Ivk95Leaves :=
  ivk95Leaves_of_unitary ivk95_u4 ivk95_u5

theorem ivk_9_5At_gh_all_proved :
    IVK_9_5At_gh_all :=
  ivk_9_5At_gh_all_of_leaves ivk95Leaves_proved

end CFSG.GH74.GLS.IVK.Proofs2
