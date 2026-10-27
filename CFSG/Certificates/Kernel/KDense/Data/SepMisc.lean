module

public import CFSG.Certificates.Kernel.KDense.Data.SepData

public section

set_option maxRecDepth 200000

namespace CFSG.KD.KDS

open CFSG.KC CFSG.KC.KDense

theorem u_bound : Nat.blt U (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 24) (Nat.mul (nat_lit 4) SX))) = true := by
  quickRfl

theorem mk_ok : mkOK (CFSG.YGroups.Y443Native.aTab ()) MK = true := by quickRfl

theorem sort_ok : sortOK QSf NS = true := by quickRfl

end CFSG.KD.KDS

end
