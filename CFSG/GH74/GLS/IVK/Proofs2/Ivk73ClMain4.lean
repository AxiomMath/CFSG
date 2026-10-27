module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClMain3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.Blueprint

theorem ivk73ClassicalOne_holds :
    Ivk73ClassicalOne where
  u4 := fun p f hp hp2 hf hmod => ivk73_u4 p f hp hp2 hf hmod

theorem ivk_7_3_g4_of_rest_zero
    (hr : Ivk73Rest) (ho : IVK73_L3U3) : IVK_7_3_g4 :=
  ivk_7_3_g4_of_rest_one hr ivk73ClassicalOne_holds ho

end CFSG.GH74.GLS.IVK
