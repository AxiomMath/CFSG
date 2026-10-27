module

public import Certificates.Data.Kernel.Misc.GL4Elt
public import CFSG.Certificates.Kernel.Misc.GL4CodeSound

public section

namespace CFSG.KC.Misc.GL4

open Matrix CFSG.KC.LQT.P CFSG.KC.Ord
open Certificates.A5GL42 (Mat4 Vec4 ofCode)

theorem pow4F_lt (c n : ℕ) : pow4F c n < 65536 := by
  cases n with
  | zero =>
    change id4 < 65536
    decide
  | succ n => exact mul4F_lt _ _

theorem ofCode_pow4F (c n : ℕ) : ofCode (pow4F c n) = ofCode c ^ n := by
  induction n with
  | zero => exact ofCode_id4
  | succ n ih =>
    change ofCode (mul4F (pow4F c n) c) = _
    rw [mul4F_ofCode, ih, pow_succ]

theorem ofCode_eq_one {c : ℕ} (hc : c < 65536) : ofCode c = 1 ↔ c = id4 := by
  constructor
  · intro h
    exact ofCode_inj hc (by decide) (h.trans ofCode_id4.symm)
  · rintro rfl
    exact ofCode_id4

theorem ofCode_xor (a b : ℕ) : ofCode (Nat.xor a b) = ofCode a + ofCode b := by
  change ofCode (a ^^^ b) = _
  ext i j
  simp only [ofCode, Matrix.of_apply, Matrix.add_apply, Nat.testBit_xor]
  cases a.testBit (4 * i.val + j.val) <;> cases b.testBit (4 * i.val + j.val) <;> decide

theorem ofCode_zero : ofCode 0 = 0 := by
  ext i j
  simp [ofCode]

end CFSG.KC.Misc.GL4

end
