module

public import Certificates.Data.Kernel.P0VisLen
public import Aesop.BuiltinRules
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.P0Vis

open CFSG.KC.P0Orb

theorem glenOK_spec {rows : List VRow} (h : glenOK rows = true) :
    ∀ row ∈ rows, ∀ c ∈ row.2, c.1.length ≤ 16 := by
  intro row hrow c hc
  rw [glenOK, List.all_eq_true] at h
  have h2 := List.all_eq_true.1 (h row hrow) c hc
  exact Nat.le_of_ble_eq_true h2

theorem fld_eq_zero {X w i n m : ℕ} (hX : X < 2 ^ (w * n)) (hi : n ≤ i) : fld X (w * i) m = 0 := by
  have h : Nat.shiftRight X (w * i) = 0 := by
    change X >>> (w * i) = 0
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hX
      (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left w hi)))
  unfold fld
  rw [h]
  exact Nat.zero_and m

theorem fc_all {dat : MonsterB.P0Rank.Data} {FK FC NF : ℕ}
    (hf : ∀ i < NF, factOK dat FK FC i = true) (hK : FK < 2 ^ (32 * NF))
    (hC : FC < 2 ^ (16 * NF)) (h0 : fval dat 0 = 0) :
    ∀ i, fld FC (16 * i) 65535 = fval dat (fld FK (32 * i) m32) := by
  intro i
  by_cases hi : i < NF
  · exact Nat.eq_of_beq_eq_true (hf i hi)
  · rw [fld_eq_zero hC (by omega), fld_eq_zero hK (by omega), h0]

end CFSG.KC.P0Vis

end
