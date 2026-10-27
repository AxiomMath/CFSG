module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TC1068
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TC1112
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TC113
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TT119F
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TTONTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TTG23
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TT1061

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

structure Tables112Cover : Prop where
  t1068 : CoverT1068
  t10112 : CoverT10112
  t10113 : CoverT10113

section Certs


theorem tables112Types_of_cover (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (C : Tables112Cover) : Tables112Types where
  T10_11_2 := tables112Types_T10_11_2_of_cover hSpM
    (tables112Types_T10_11_3_of_cover hGA C.t10113) C.t10112
  T10_11_3 := tables112Types_T10_11_3_of_cover hGA C.t10113
  T10_6_8 := tables112Types_T10_6_8_of_cover hSpM C.t1068
  TON := tables112Types_TON_holds
  TG23 := tables112Types_TG23_holds
  T10_6_1 := tables112Types_T10_6_1_holds
  T11_9 := tables112Types_T11_9_holds
  T11_9F := tables112Types_T11_9F_holds
  T10_10 := tables112Types_T10_10_holds

end Certs

end CFSG.HardMathSupport.Solomon.Coordinator
