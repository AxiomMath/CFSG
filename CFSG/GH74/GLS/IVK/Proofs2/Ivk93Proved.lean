module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Assembly
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L5
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93U4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93U5

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint

theorem ivk93Leaves_proved :
    Ivk93Leaves :=
  ivk93Leaves_of_four ivk93_l4 ivk93_u4 ivk93_l5 ivk93_u5

theorem ivk93Pair_proved :
    Ivk93Pair :=
  ivk93Pair_of_leaves ivk93Leaves_proved

end CFSG.GH74.GLS.IVK.Proofs2
