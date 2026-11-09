module

public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Certificates.Kernel.Enum.DefsC

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS

theorem div_mod_div_mod (x a b c w : Nat) (h : b + w ≤ c) :
    x / 2 ^ a % 2 ^ c / 2 ^ b % 2 ^ w = x / 2 ^ (a + b) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · have h2 : i + b < c := by omega
    simp only [hi, h2, decide_true, Bool.true_and]
    rw [Nat.add_assoc, Nat.add_comm b a]
  · simp [hi]

theorem fld_fld (x a b c w : Nat) (h : b + w ≤ c) :
    Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight x a) (mask c)) b) (mask w) =
      Nat.land (Nat.shiftRight x (a + b)) (mask w) := by
  rw [fld_eq, fld_eq, fld_eq, div_mod_div_mod x a b c w h]

theorem rdC_eq (w p j : Nat) : rdC w (mask w) p j = Nat.land (Nat.shiftRight p (Nat.mul w j)) (mask w) := by
  unfold rdC
  rw [strictN_eq]
  have h15 : Nat.land j 15 ≤ 15 := Nat.and_le_right
  have hb : Nat.mul w (Nat.land j 15) + w ≤ Nat.mul w 16 := by
    simp only [Nat.mul_eq]
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left w (by omega)
  have e := fld_fld p (Nat.mul (Nat.mul w 16) (Nat.shiftRight j 4)) (Nat.mul w (Nat.land j 15))
    (Nat.mul w 16) w hb
  refine e.trans ?_
  congr 2
  have h1 : Nat.shiftRight j 4 = j / 16 := Nat.shiftRight_eq_div_pow j 4
  have h2 : Nat.land j 15 = j % 16 := Nat.and_two_pow_sub_one_eq_mod j 4
  rw [h1, h2]
  simp only [Nat.mul_eq]
  have := Nat.div_add_mod j 16
  rw [Nat.mul_assoc, ← Nat.mul_add, this]

theorem chunkQ_eq (w q lo k : Nat) (hk : k < 8) :
    Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight q (Nat.mul w lo))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul w 8)) 1))
      (Nat.mul w k)) (mask w) = Nat.land (Nat.shiftRight q (Nat.mul w (Nat.add lo k))) (mask w) := by
  have hb : Nat.mul w k + w ≤ Nat.mul w 8 := by
    simp only [Nat.mul_eq]
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left w (by omega)
  rw [show Nat.sub (Nat.shiftLeft 1 (Nat.mul w 8)) 1 = mask (Nat.mul w 8) from rfl, fld_fld q _ _ _ w hb]
  congr 2
  simp only [Nat.mul_eq, Nat.add_eq, Nat.mul_add]

theorem chunkQ_eq0 (w q lo : Nat) :
    Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight q (Nat.mul w lo))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul w 8)) 1))
      (Nat.mul w (nat_lit 0))) (mask w) = Nat.land (Nat.shiftRight q (Nat.mul w lo)) (mask w) := by
  rw [chunkQ_eq w q lo (nat_lit 0) (by decide)]
  rfl

theorem leafC_eq (w p q lo : Nat) : leafC w (mask w) p q lo = pmkH8 w (mask w) p q 0 lo := by
  unfold leafC
  rw [strictN_eq]
  change Nat.lor _ _ = Nat.lor _ _
  simp only [rdC_eq, chunkQ_eq0, chunkQ_eq w q lo (nat_lit 1) (by decide), chunkQ_eq w q lo (nat_lit 2) (by decide),
    chunkQ_eq w q lo (nat_lit 3) (by decide), chunkQ_eq w q lo (nat_lit 4) (by decide),
    chunkQ_eq w q lo (nat_lit 5) (by decide), chunkQ_eq w q lo (nat_lit 6) (by decide),
    chunkQ_eq w q lo (nat_lit 7) (by decide)]

theorem pmkC_eq (w p q : Nat) : ∀ d lo, pmkC w (mask w) p q d lo = pmkH8 w (mask w) p q d lo := by
  intro d
  induction d with
  | zero => exact leafC_eq w p q
  | succ d ih =>
    intro lo
    change Nat.lor (pmkC w (mask w) p q d lo)
        (Nat.shiftLeft (pmkC w (mask w) p q d (Nat.add lo (Nat.shiftLeft 8 d)))
          (Nat.mul w (Nat.shiftLeft 8 d))) =
      Nat.lor (pmkH8 w (mask w) p q d lo)
        (Nat.shiftLeft (pmkH8 w (mask w) p q d (Nat.add lo (Nat.shiftLeft 8 d)))
          (Nat.mul w (Nat.shiftLeft 8 d)))
    rw [ih, ih]

theorem pcompC_eq (n w p q : Nat) : pcompC n w (mask w) p q = pcomp n w (mask w) p q := by
  have h : pmkC w (mask w) p q = pmkH8 w (mask w) p q :=
    funext fun d => funext fun lo => pmkC_eq w p q d lo
  unfold pcompC
  rw [h]
  rfl

end CFSG.KS.PK

end
