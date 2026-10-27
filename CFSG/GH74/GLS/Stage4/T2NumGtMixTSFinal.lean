module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLayer
public import CFSG.GH74.GLS.Stage4.T2NumGtMixTSMain
public import CFSG.GH74.GLS.Stage4.T2NumGtMixTSSing

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem ch6Mix_ts
    (hL : SDWreathedLayer) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    Ch6MixTS :=
  ch6Mix_ts_of_steps ch6Mix_sing (ch6Mix_layer hL hGA)

end CFSG.GH74.GLS.Stage4.Rest
