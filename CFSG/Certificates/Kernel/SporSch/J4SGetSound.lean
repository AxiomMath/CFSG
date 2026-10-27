module

public import CFSG.Certificates.Kernel.SporSch.J4SPairSound
import CFSG.Certificates.Kernel.SporSch.J4SFormSound

public section

namespace CFSG.KS.SporSch.J4B

open CFSG.KC.J4Q

theorem get_enc {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (_hX : WfN X) {r : Nat}
    (_hr : r < 112) : X[r]! = rowJ rm (encN X) r := by
  obtain ⟨-, hrm⟩ := consts_c _hK
  subst hrm
  have hr' : r < X.size := _hX.1 ▸ _hr
  have hx : X[r]! < 2 ^ 112 := _hX.2 r _hr
  have e0 : X[r]?.getD 0 = X[r]! := by
    rw [getElem?_pos X r hr', Option.getD_some, getElem!_pos X r hr']
  apply Nat.eq_of_testBit_eq
  intro j
  change _ = ((encN X >>> (r * 128)) &&& (2 ^ 112 - 1)).testBit j
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, encN_bit _hX]
  by_cases hj : j < 112
  · have e1 : (r * 128 + j) / 128 = r := by omega
    have e2 : (r * 128 + j) % 128 = j := by omega
    rw [e1, e2, e0]
    simp [_hr, hj]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hj]

theorem dropI_eq : ∀ (n : Nat) (l : List Int), dropI n l = l.drop n
  | 0, _ => rfl
  | n + 1, [] => by
    change dropI n [] = _
    rw [dropI_eq n []]
    simp
  | n + 1, _ :: t => by
    change dropI n t = _
    rw [dropI_eq n t]
    rfl

theorem takeI_eq : ∀ (n : Nat) (l : List Int), takeI n l = l.take n
  | _, [] => by cases ‹Nat› <;> rfl
  | 0, _ :: _ => rfl
  | n + 1, x :: t => by
    change x :: takeI n t = _
    rw [takeI_eq n t]
    rfl

end CFSG.KS.SporSch.J4B

end
