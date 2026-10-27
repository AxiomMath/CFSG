module

public import Certificates.Data.Kernel.Misc.TitsBridge
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.KC.TitsBridge

open CFSG.KC.Enum CFSG.KS CFSG.Open

theorem fw_zero (a b c d : Nat) (t : List Nat) :
    quasithinFixedWidth 4 (a :: b :: c :: d :: t) 0 =
      10 * (10 * (10 * (10 * 0 + a) + b) + c) + d := rfl

theorem fw_succ (a b c d : Nat) (t : List Nat) (j : Nat) :
    quasithinFixedWidth 4 (a :: b :: c :: d :: t) (j + 1) = quasithinFixedWidth 4 t j := by
  have h : ∀ r, (a :: b :: c :: d :: t).getD (4 * (j + 1) + r) 0 = t.getD (4 * j + r) 0 := by
    intro r
    have e : 4 * (j + 1) + r = (4 * j + r) + 1 + 1 + 1 + 1 := by ring
    rw [e]
    simp only [List.getD_cons_succ]
  simp only [quasithinFixedWidth, h]

theorem cmp4_sound (P : Nat) : ∀ (k : Nat) (l : List Nat), cmp4 P k l = true →
    ∀ j, k + j < 1755 → quasithinFixedWidth 4 l j % 1755 = pg 11 (mask 11) P (k + j)
  | k, a :: b :: c :: d :: t, h, j, hj => by
    simp only [cmp4, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => rw [fw_zero]; exact h.1
    | succ j =>
      rw [fw_succ, cmp4_sound P (k + 1) t h.2 j (by omega)]
      congr 1
      omega
  | k, [], h, j, hj => by
    simp only [cmp4, beq_iff_eq] at h
    omega
  | _, [_], h, _, _ => by simp [cmp4] at h
  | _, [_, _], h, _, _ => by simp [cmp4] at h
  | _, [_, _, _], h, _, _ => by simp [cmp4] at h

theorem digitsK_eq (cs : List Char) : quasithinDigits (String.ofList cs) = digitsK cs := by
  rw [quasithinDigits, String.toList_ofList]
  rfl

end CFSG.KC.TitsBridge

end
