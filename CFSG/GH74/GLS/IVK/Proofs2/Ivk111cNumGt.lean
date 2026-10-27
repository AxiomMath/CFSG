module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cFinal
public import CFSG.GH74.GLS.Stage4.T2NumGtMixNumGt

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem ch6T2NumGt_proved
    (hL : SDWreathedLayer) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    Ch6T2NumGt :=
  ch6T2NumGt_of_11c hL hGA IVK.Proofs2.ivk_11_1c_fixed

end CFSG.GH74.GLS.Stage4.Rest
