module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDFinal
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cCMain
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cKTop
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cNMain
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cAInj
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cTFinrank
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cTTwist

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.Stage4.Rest

theorem ivk_11_1c_fixed : IVK_11_1c_fixed :=
  ivk_11_1c_fixed_of_sl2class
    (mix11c_sl2class
      (mix11c_descent
        (mix11cSteinberg_of steinberg_simple_holds steinberg_finrank_holds steinberg_negOne_holds
          steinberg_end_holds steinberg_twist_holds steinberg_inj_holds
          (steinberg_complete_of steinberg_simple_holds steinberg_inj_holds)))
      mix11c_numerics_holds)

end CFSG.GH74.GLS.IVK.Proofs2
