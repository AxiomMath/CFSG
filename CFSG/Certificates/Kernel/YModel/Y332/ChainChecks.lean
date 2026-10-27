module

public import CFSG.Certificates.Kernel.YModel.Y332.Chain
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.YMY332

open CFSG.KC.YModel

@[expose] noncomputable def ch10099word (i : Nat) : Bool := wordOK 15 32 9 T0 WP0 WL0 i

@[expose] noncomputable def ch10099lev (i : Nat) : Bool :=
  levelOK 15 28162 21 T0 (CFSG.KD.YM332C.F 0) R0 M0 Z0 i

#kc_each ch10099word 0 12
#kc_each ch10099lev 0 9

@[expose] noncomputable def ch10099swap (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (T0 j) (T0 9) (Nat.beq j 10))
    (T0 10) (Nat.beq j 9)

@[expose] noncomputable def ch10099cut (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (M0 i) (Nat.xor (M0 1) (Nat.shiftLeft 1 5)) (Nat.beq i 1)

theorem ch10099neg :
    (!wordOK 15 32 9 ch10099swap WP0 WL0 0 &&
      !levelOK 15 28162 21 T0 (CFSG.KD.YM332C.F 0) R0 ch10099cut Z0 1 &&
      !levelOK 15 28162 21 T0 (CFSG.KD.YM332C.F 0) R0 M0 (fun i => Nat.succ (Z0 i)) 3) = true := by
  quickRfl

end CFSG.KD.YMY332

end
