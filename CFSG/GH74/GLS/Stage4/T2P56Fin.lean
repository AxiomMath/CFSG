module

public import CFSG.GH74.GLS.Stage4.T2P56Three
public import CFSG.GH74.GLS.Stage4.T2P56M11

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem noM11Layer : NoM11Layer := by
  intro Y _ _ ψ E _ hEodd hE hSD K hKE hK z hzK hz2 hψK hψ2
  exact no_m11_layer ψ E hEodd hE hSD hKE hK hzK hz2 hψK hψ2

theorem ch6T2Prop56Gt_of_layer_gA
    (hL : SDWreathedLayer)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : Ch6T2Prop56Gt :=
  ch6T2Prop56Gt_of_layer hL (LU.Local.l3Cover hGA) (threeCaseJ_of_layer hL hGA noM11Layer)

theorem ch6T2Prop56Eq_of_layer_gA (hL : SDWreathedLayer)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : Ch6T2Prop56Eq :=
  ch6T2Prop56Eq_of_layer hL (LU.Local.l3Cover hGA)

end CFSG.GH74.GLS.Stage4.Rest
