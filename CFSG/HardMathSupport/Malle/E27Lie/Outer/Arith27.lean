module

public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Open

theorem twentySeven_dvd_ordG2 (q : ℕ) (hq : 1 ≤ q) : 27 ∣ ordG2 q := by
  unfold ordG2
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  generalize (q : ZMod 27) = x
  revert x
  decide +kernel

theorem twentySeven_dvd_ordF4 (q : ℕ) (hq : 1 ≤ q) : 27 ∣ ordF4 q := by
  unfold ordF4
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  generalize (q : ZMod 27) = x
  revert x
  decide +kernel

theorem twentySeven_dvd_ordE8 (q : ℕ) (hq : 1 ≤ q) : 27 ∣ ordE8 q := by
  unfold ordE8
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  generalize (q : ZMod 27) = x
  revert x
  decide +kernel

theorem eightyOne_dvd_numE6 (q : ℕ) (hq : 1 ≤ q) :
    81 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1) := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  generalize (q : ZMod 81) = x
  revert x
  decide +kernel

theorem twentySeven_dvd_numE7 (q : ℕ) (hq : 1 ≤ q) :
    27 ∣ q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 2 - 1) := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  generalize (q : ZMod 27) = x
  revert x
  decide +kernel

theorem twentySeven_dvd_numTwistedF4 (q : ℕ) (hq : q % 3 = 2) :
    27 ∣ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) := by
  have hq1 : 1 ≤ q := by omega
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_sub hq1]
  have h : (q : ZMod 27).val % 3 = 2 := by
    rw [ZMod.val_natCast]
    omega
  generalize (q : ZMod 27) = x at h ⊢
  revert x
  decide +kernel

end CFSG.HardMathSupport.Malle.E27Lie
