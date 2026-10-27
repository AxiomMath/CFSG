module

public import CFSG.Certificates.Kernel.MonsterB.FischerKSound

public section

namespace CFSG.KC.FischerE

open CFSG.KLie.CT CFSG.KC.FischerK

theorem fget_eq' (X i w : Nat) : fget X i w = X >>> (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& ((1 <<< w) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]

theorem fget_xor (a b i w : Nat) : fget (a ^^^ b) i w = fget a i w ^^^ fget b i w := by
  rw [fget_eq', fget_eq', fget_eq']
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_xor]
  cases decide (j < w) <;> simp

theorem fget_zero (i w : Nat) : fget 0 i w = 0 := by
  rw [fget_eq']
  simp

theorem fget_vecMulL (c w : Nat) : ∀ (R : List Nat) (v : Nat),
    fget (vecMulL R v) c w = vecMulL (R.map fun r => fget r c w) v
  | [], v => by
    rw [List.map_nil, vecMulL_nil, fget_zero]
  | r :: R, v => by
    rw [List.map_cons, vecMulL_cons, vecMulL_cons, fget_xor, fget_vecMulL c w R]
    by_cases hb : v.testBit 0
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb, fget_zero]

theorem fget_big {M w n m : Nat} (hM : M < 2 ^ (w * n)) (hm : n ≤ m) : fget M m w = 0 := by
  rw [fget_eq']
  have h2 : M >>> (m * w) = 0 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
    calc M < 2 ^ (w * n) := hM
      _ ≤ 2 ^ (m * w) := Nat.pow_le_pow_right (by omega) (by
        rw [Nat.mul_comm w]
        exact Nat.mul_le_mul_right w hm)
  rw [h2]
  rfl

theorem packW_get_all {w M : Nat} {L : List Nat} (h : packW w M L 0 = true)
    (hM : M < 2 ^ (w * L.length)) (m : Nat) : L.toArray[m]! = fget M m w := by
  by_cases hm : m < L.length
  · exact packW_get h hm
  · have h1 : L.toArray[m]! = 0 := by
      rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [h1, fget_eq']
    have h2 : M >>> (m * w) = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
      calc M < 2 ^ (w * L.length) := hM
        _ ≤ 2 ^ (m * w) := Nat.pow_le_pow_right (by omega) (by
          rw [Nat.mul_comm w]
          exact Nat.mul_le_mul_right w (by omega))
    rw [h2]
    rfl

end CFSG.KC.FischerE

end
