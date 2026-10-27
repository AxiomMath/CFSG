module

public import CFSG.GH74.GLS.Stage4.T2NegFin3
public import CFSG.GH74.GLS.Stage4.T2NegCfgThree
public import CFSG.GH74.GLS.Stage4.T2NegRU3

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS

theorem ch6T2TSingEq2_proved (h3 : Ch6T2P51) (h4 : Ch6T2P52)
    (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover) : Ch6T2TSingEq2 :=
  ch6T2TSingEq2_of_leaves h3 h4 ⟨ch6T2NegCfgMod_one, ch6T2NegCfgMod_three⟩ hL hL3
    IVK.Proofs2.ivk_4_1_R_U3

end CFSG.GH74.GLS.Stage4.Rest
