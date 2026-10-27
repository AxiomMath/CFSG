module

public import CFSG.Certificates.Kernel.Asc82Syl.Codes

public section

namespace CFSG.KS.Asc82Syl

variable (A : Nat → Matrix (Fin 6) (Fin 6) (ZMod 3))

noncomputable def Rm (k : Nat) : Nat → Nat → Matrix (Fin 6) (Fin 6) (ZMod 3)
  | 0, _ => 1
  | l + 1, e => Rm k l e * (if e.testBit (k + l) then A (k + l) else 1)

theorem Wm_add (k : Nat) : ∀ l e, Wm A (k + l) e = Wm A k e * Rm A k l e
  | 0, e => by rw [Nat.add_zero, Rm, mul_one]
  | l + 1, e => by
    rw [← Nat.add_assoc, Wm_succ, Wm_add k l e, Rm, mul_assoc]

theorem Rm_congr (k : Nat) : ∀ l e e', (∀ i < l, e.testBit (k + i) = e'.testBit (k + i)) →
    Rm A k l e = Rm A k l e'
  | 0, _, _, _ => rfl
  | l + 1, e, e', h => by
    simp only [Rm]
    rw [Rm_congr k l e e' (fun i hi => h i (by omega)), h l (by omega)]

theorem Wm_zero_bits : ∀ k e, (∀ i < k, e.testBit i = false) → Wm A k e = 1
  | 0, e, _ => Wm_zero A e
  | k + 1, e, h => by
    rw [Wm_succ, Wm_zero_bits k e (fun i hi => h i (by omega)), h k (by omega)]
    simp

theorem Rm_zero_bits (k : Nat) : ∀ l e, (∀ i < l, e.testBit (k + i) = false) → Rm A k l e = 1
  | 0, _, _ => rfl
  | l + 1, e, h => by
    rw [Rm, Rm_zero_bits k l e (fun i hi => h i (by omega)), h l (by omega)]
    simp

theorem Wm_split (k l e : Nat) :
    Wm A (k + l) e = Wm A (k + l) (e % 2 ^ k) * Wm A (k + l) (e / 2 ^ k * 2 ^ k) := by
  rw [Wm_add, Wm_add, Wm_add]
  have h1 : Wm A k (e % 2 ^ k) = Wm A k e :=
    Wm_congr A k _ _ (fun i hi => by rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and])
  have h2 : Rm A k l (e % 2 ^ k) = 1 :=
    Rm_zero_bits A k l _ (fun i _ => by
      rw [Nat.testBit_mod_two_pow, decide_eq_false (by omega), Bool.false_and])
  have h3 : Wm A k (e / 2 ^ k * 2 ^ k) = 1 :=
    Wm_zero_bits A k _ (fun i hi => by
      rw [Nat.testBit_mul_two_pow, decide_eq_false (by omega), Bool.false_and])
  have h4 : Rm A k l (e / 2 ^ k * 2 ^ k) = Rm A k l e :=
    Rm_congr A k l _ _ (fun i _ => by
      rw [Nat.testBit_mul_two_pow, decide_eq_true (by omega), Bool.true_and,
        Nat.testBit_div_two_pow, Nat.add_sub_cancel_left, Nat.add_comm])
  rw [h1, h2, h3, h4, mul_one, one_mul]

end CFSG.KS.Asc82Syl

end
