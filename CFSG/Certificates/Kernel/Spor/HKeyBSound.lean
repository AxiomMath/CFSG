module

public import Certificates.Data.Kernel.Spor.HKeyB
public import CFSG.Certificates.Kernel.Spor.MulHSound
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

theorem mask_eqB (w : Nat) : mask w = 2 ^ w - 1 := by
  change (1 <<< w) - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem hkGo_zero (w m X i h : Nat) : hkGo w m X 0 i h = h := rfl

theorem hkGo_add (w m X b : Nat) : ∀ a i h,
    hkGo w m X (a + b) i h = hkGo w m X b (i + a) (hkGo w m X a i h)
  | 0, i, h => by rw [Nat.zero_add, Nat.add_zero, hkGo_zero]
  | a + 1, i, h => by
    rw [Nat.add_right_comm, hkGo_succ, hkGo_add w m X b a, hkGo_succ, Nat.add_right_comm i 1 a,
      Nat.add_assoc]

theorem pg_shiftB (w X o j : Nat) :
    pg w (mask w) (X >>> (w * o)) j = pg w (mask w) X (o + j) := by
  change ((X >>> (w * o)) >>> (w * j)) &&& mask w = (X >>> (w * (o + j))) &&& mask w
  rw [Nat.mul_add, Nat.shiftRight_add]

theorem pg_blk64 (w X b j : Nat) (hj : j < 64) :
    pg w (mask w) (blk64 w X b) j = pg w (mask w) X (64 * b + j) := by
  change (((X >>> (w * 64 * b)) &&& mask (w * 64)) >>> (w * j)) &&& mask w =
    (X >>> (w * (64 * b + j))) &&& mask w
  rw [mask_eqB, mask_eqB, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow]
  have e1 : 2 ^ (w * 64) = 2 ^ (w * j) * 2 ^ (w * 64 - w * j) := by
    have : w * j ≤ w * 64 := Nat.mul_le_mul_left w (by omega)
    rw [← Nat.pow_add]
    congr 1
    omega
  have hdvd : 2 ^ w ∣ 2 ^ (w * 64 - w * j) := by
    apply Nat.pow_dvd_pow
    have : w * j + w ≤ w * 64 := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left w (by omega)
    omega
  have e3 : w * 64 * b + w * j = w * (64 * b + j) := by rw [Nat.mul_add, Nat.mul_assoc]
  rw [e1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd, Nat.div_div_eq_div_mul,
    ← Nat.pow_add, e3]

theorem hkGo_blk64 (w X b : Nat) : ∀ len j h, j + len ≤ 64 →
    hkGo w (mask w) (blk64 w X b) len j h = hkGo w (mask w) X len (64 * b + j) h
  | 0, _, _, _ => rfl
  | len + 1, j, h, hl => by
    rw [hkGo_succ, hkGo_succ, pg_blk64 w X b j (by omega), hkGo_blk64 w X b len (j + 1) _ (by omega),
      Nat.add_assoc]

theorem hkGo_shiftB (w X o : Nat) : ∀ len j h,
    hkGo w (mask w) (X >>> (w * o)) len j h = hkGo w (mask w) X len (o + j) h
  | 0, _, _ => rfl
  | len + 1, j, h => by
    rw [hkGo_succ, hkGo_succ, pg_shiftB, hkGo_shiftB w X o len (j + 1), Nat.add_assoc]

theorem hkBl_eq (w X : Nat) : ∀ nb j h,
    hkBl w (mask w) X nb j h = hkGo w (mask w) X (64 * nb) (64 * j) h
  | 0, _, _ => rfl
  | nb + 1, j, h => by
    change strictN (hkGo w (mask w) (blk64 w X j) 64 0 h) (fun h' => hkBl w (mask w) X nb (j + 1) h')
      = _
    have e : 64 * (nb + 1) = 64 + 64 * nb := by omega
    rw [CFSG.KS.PF.strictN_eqP, hkBl_eq w X nb (j + 1), hkGo_blk64 w X j 64 0 h (by omega), e,
      hkGo_add, Nat.mul_succ]
    rfl

theorem hkeyB_eq (n w X : Nat) : hkeyB n w (mask w) X = hkeyK n w (mask w) X := by
  change strictN (hkBl w (mask w) X (n >>> 6) 0 14695981039346656037)
      (fun h => hkGo w (mask w) (X >>> (w * 64 * (n >>> 6))) (n &&& 63) 0 h) =
    hkGo w (mask w) X n 0 14695981039346656037
  rw [CFSG.KS.PF.strictN_eqP, hkBl_eq, Nat.mul_assoc, hkGo_shiftB, Nat.mul_zero, Nat.add_zero]
  have hadd := hkGo_add w (mask w) X (n &&& 63) (64 * (n >>> 6)) 0 14695981039346656037
  rw [Nat.zero_add] at hadd
  rw [← hadd]
  congr 1
  rw [Nat.shiftRight_eq_div_pow, (by decide : (63 : Nat) = 2 ^ 6 - 1),
    Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.div_add_mod n (2 ^ 6)
  simpa using this

theorem hkeyB_tabT {n w X : Nat} (hX : canonK n w (mask w) (n * w) X = true) :
    (CFSG.Sporadic.SmallOddCore.Native.hkey n (tabT (unpack n w X))).toNat =
      hkeyB n w (mask w) X := by
  rw [hkeyB_eq, hkey_tabT hX]

end CFSG.KS.MulH

end
