module

public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import Certificates.Data.Kernel.KDense.Init
public import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import CFSG.Certificates.Kernel.KDense.Tactic

public section

namespace CFSG.KD.KDF

open CFSG.KC CFSG.KC.KDense

set_option maxRecDepth 200000

theorem th_ok : thOK TH = true := by quickRfl

theorem oct_ok : octOK OCT = true := by quickRfl

theorem du1_ok : du1OK DU1 = true := by quickRfl

theorem keys0 : keyRange TH OCT DU1 (nat_lit 14) (keySlice KT (nat_lit 0)) (Nat.mul (nat_lit 0) (nat_lit 16384)) =
  true := by quickRfl
theorem keys1 : keyRange TH OCT DU1 (nat_lit 14) (keySlice KT (nat_lit 1)) (Nat.mul (nat_lit 1) (nat_lit 16384)) =
  true := by quickRfl
theorem keys2 : keyRange TH OCT DU1 (nat_lit 14) (keySlice KT (nat_lit 2)) (Nat.mul (nat_lit 2) (nat_lit 16384)) =
  true := by quickRfl
theorem keys3 : keyRange TH OCT DU1 (nat_lit 14) (keySlice KT (nat_lit 3)) (Nat.mul (nat_lit 3) (nat_lit 16384)) =
  true := by quickRfl
theorem keys4 : keyRange TH OCT DU1 (nat_lit 14) (keySlice KT (nat_lit 4)) (Nat.mul (nat_lit 4) (nat_lit 16384)) =
  true := by quickRfl
theorem keys5 : keyRange TH OCT DU1 (nat_lit 14) (keySlice KT (nat_lit 5)) (Nat.mul (nat_lit 5) (nat_lit 16384)) =
  true := by quickRfl
theorem keys6 : keyRange TH OCT DU1 (nat_lit 14) (keySlice KT (nat_lit 6)) (Nat.mul (nat_lit 6) (nat_lit 16384)) =
  true := by quickRfl
theorem keys7 : keyRange TH OCT DU1 (nat_lit 14) (keySlice KT (nat_lit 7)) (Nat.mul (nat_lit 7) (nat_lit 16384)) =
  true := by quickRfl

theorem keys_ok : keysOK TH OCT DU1 KT = true := by
  kd_andB keys7 keys6 keys5 keys4 keys3 keys2 keys1 keys0

theorem keyPlanes_ok : keyPlanesOK F KT = true := by quickRfl

theorem fix_ok : fixOK F = true := by quickRfl

theorem init_a : aInitOK (CFSG.YGroups.Y443Native.aTab ()) (I (nat_lit 0)) = true := by quickRfl

theorem init_b : rangeInitOK (nat_lit 300) (nat_lit 98580) (I (nat_lit 1)) = true := by quickRfl

theorem init_w : rangeInitOK (nat_lit 98580) (nat_lit 98581) (I (nat_lit 2)) = true := by quickRfl

end CFSG.KD.KDF

end
