module

public import Certificates.Data.Kernel.Spor.HKeyU
public import CFSG.Certificates.Kernel.Spor.HKeyBSound
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

theorem hk4_eq (w B h : Nat) : hk4 w (mask w) B h = hkGo w (mask w) B 4 0 h := by
  rw [hkGo_succ, hkGo_succ, hkGo_succ, hkGo_succ, hkGo_zero]
  change hkStep (hkStep (hkStep (hkStep h (B &&& mask w)) ((B >>> w) &&& mask w))
      ((B >>> (2 * w)) &&& mask w)) ((B >>> (3 * w)) &&& mask w) =
    hkStep (hkStep (hkStep (hkStep h ((B >>> (w * 0)) &&& mask w)) ((B >>> (w * (0 + 1))) &&& mask w))
      ((B >>> (w * (0 + 1 + 1))) &&& mask w)) ((B >>> (w * (0 + 1 + 1 + 1))) &&& mask w)
  rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.zero_add, Nat.mul_one,
    (by omega : w * (1 + 1) = 2 * w), (by omega : w * (1 + 1 + 1) = 3 * w)]

theorem hk8_eq (w B h : Nat) :
    hk4 w (mask w) (B >>> (4 * w)) (hk4 w (mask w) B h) = hkGo w (mask w) B 8 0 h := by
  rw [hk4_eq, hk4_eq, Nat.mul_comm 4 w, hkGo_shiftB, Nat.add_zero,
    (by rfl : (8 : Nat) = 4 + 4), hkGo_add, Nat.zero_add]

theorem hkU8_eq (w : Nat) : ∀ k B h, hkU8 w (mask w) k B h = hkGo w (mask w) B (8 * k) 0 h
  | 0, _, _ => rfl
  | k + 1, B, h => by
    change strictN (B >>> (8 * w)) (fun B' => strictN (hk4 w (mask w) (B >>> (4 * w))
      (hk4 w (mask w) B h)) (fun h' => hkU8 w (mask w) k B' h')) = _
    rw [CFSG.KS.PF.strictN_eqP, CFSG.KS.PF.strictN_eqP, hkU8_eq w k, hk8_eq, Nat.mul_comm 8 w,
      hkGo_shiftB, Nat.add_zero, (by omega : 8 * (k + 1) = 8 + 8 * k), hkGo_add, Nat.zero_add]

theorem hkBlU_eq (w X : Nat) : ∀ nb j h, hkBlU w (mask w) X nb j h = hkBl w (mask w) X nb j h
  | 0, _, _ => rfl
  | nb + 1, j, h => by
    change strictN (hkU8 w (mask w) 8 (blk64 w X j) h) (fun h' => hkBlU w (mask w) X nb (j + 1) h') =
      strictN (hkGo w (mask w) (blk64 w X j) 64 0 h) (fun h' => hkBl w (mask w) X nb (j + 1) h')
    rw [CFSG.KS.PF.strictN_eqP, CFSG.KS.PF.strictN_eqP, hkBlU_eq w X nb, hkU8_eq]

theorem hkeyU_eq (n w X : Nat) : hkeyU n w (mask w) X = hkeyK n w (mask w) X := by
  rw [← hkeyB_eq]
  change strictN (hkBlU w (mask w) X (n >>> 6) 0 14695981039346656037)
      (fun h => hkGo w (mask w) (X >>> (w * 64 * (n >>> 6))) (n &&& 63) 0 h) =
    strictN (hkBl w (mask w) X (n >>> 6) 0 14695981039346656037)
      (fun h => hkGo w (mask w) (X >>> (w * 64 * (n >>> 6))) (n &&& 63) 0 h)
  rw [hkBlU_eq]

end CFSG.KS.MulH

end
