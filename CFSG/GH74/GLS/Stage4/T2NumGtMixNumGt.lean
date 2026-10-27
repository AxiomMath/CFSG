module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixFinal
public import CFSG.GH74.GLS.Stage4.T2NumGtGlue
public import CFSG.GH74.GLS.Stage4.T2RemProof
public import CFSG.GH74.GLS.Stage4.T2P52Done

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem ch6T2NumGt_of_11c
    (hL : SDWreathedLayer) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h11c : IVK.Proofs2.IVK_11_1c_fixed) : Ch6T2NumGt :=
  ch6T2NumGt_of_leaves Rem.ch6T2Rem_proved ch6T2P51 ch6T2P52 ch6T2P53 hL hGA (ivk_11_1c_dim_of_fixed h11c)
    (ch6Gt_mixed_proved Rem.ch6T2Rem_proved hL hGA)

end CFSG.GH74.GLS.Stage4.Rest
