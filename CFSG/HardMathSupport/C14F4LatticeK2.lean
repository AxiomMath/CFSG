module

public import CFSG.HardMathSupport.C14F4LatticeCheck

public section

namespace CFSG.HardMathSupport.C14F4LatticeCheck

theorem rank2OK_0 : ((f4Pos.sublistsLen 2).take 35).all rank2F = true := by decide +kernel

theorem rank2OK_1 : (((f4Pos.sublistsLen 2).drop 35).take 35).all rank2F = true := by decide +kernel

theorem rank2OK_2 : ((((f4Pos.sublistsLen 2).drop 35).drop 35).take 35).all rank2F = true := by decide +kernel

theorem rank2OK_3 : (((((f4Pos.sublistsLen 2).drop 35).drop 35).drop 35).take 35).all rank2F = true := by decide +kernel

theorem rank2OK_4 : ((((((f4Pos.sublistsLen 2).drop 35).drop 35).drop 35).drop 35).take 35).all rank2F = true := by decide +kernel

theorem rank2OK_5 : (((((((f4Pos.sublistsLen 2).drop 35).drop 35).drop 35).drop 35).drop 35).take 35).all rank2F = true := by decide +kernel

theorem rank2OK_6 : ((((((((f4Pos.sublistsLen 2).drop 35).drop 35).drop 35).drop 35).drop 35).drop 35).take 35).all rank2F = true := by decide +kernel

theorem rank2OK_7 : ((((((((f4Pos.sublistsLen 2).drop 35).drop 35).drop 35).drop 35).drop 35).drop 35).drop 35).all rank2F = true := by decide +kernel

theorem rank2OK_eq : rank2OK = true := by
  unfold rank2OK
  refine all_eq_true_of_take_drop 35 rank2OK_0 ?_
  refine all_eq_true_of_take_drop 35 rank2OK_1 ?_
  refine all_eq_true_of_take_drop 35 rank2OK_2 ?_
  refine all_eq_true_of_take_drop 35 rank2OK_3 ?_
  refine all_eq_true_of_take_drop 35 rank2OK_4 ?_
  refine all_eq_true_of_take_drop 35 rank2OK_5 ?_
  refine all_eq_true_of_take_drop 35 rank2OK_6 ?_
  exact rank2OK_7

end CFSG.HardMathSupport.C14F4LatticeCheck
