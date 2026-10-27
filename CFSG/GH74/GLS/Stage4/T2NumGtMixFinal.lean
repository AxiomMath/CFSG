module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocMain
public import CFSG.GH74.GLS.Stage4.T2NumGtMixSecF5
public import CFSG.GH74.GLS.Stage4.T2NumGtMixSecWeyl
public import CFSG.GH74.GLS.Stage4.T2NumGtMixTSFinal
public import CFSG.GH74.GLS.Stage4.T2NumGtMixGlue

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem ch6Mix_secEx :
    Ch6MixSecEx :=
  ch6Mix_secEx_of_steps ch6Mix_loc ch6Mix_f5 ch6Mix_weyl

theorem ch6Gt_mixed_proved
    (h1 : Ch6T2Rem) (hL : SDWreathedLayer)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : Ch6GtMixed :=
  ch6Gt_mixed_of_leaves h1 ch6Mix_secEx (ch6Mix_ts hL hGA)

end CFSG.GH74.GLS.Stage4.Rest
