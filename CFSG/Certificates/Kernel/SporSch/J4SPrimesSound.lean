
module

public import CFSG.Certificates.Kernel.SporSch.J4SPowSound
public import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum CFSG.Sporadic.J4Schreier

theorem sN_p (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem appK_lt_p (P a : Nat) : appK P a < 2 ^ 11 := by
  suffices h : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a j) (nat_lit 1))
        (nat_lit 1), Nat.xor s (colK P j), s))) n < 2 ^ 11 from h 11
  intro n
  induction n with
  | zero => exact Nat.two_pow_pos 11
  | succ n ih =>
    change strictN _ _ < _
    rw [sN_p]
    cases Nat.beq (Nat.land (Nat.shiftRight a n) 1) 1
    · exact ih
    · exact Nat.xor_lt_two_pow ih (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))

theorem fld_packR_p (f : Nat → Nat) (hf : ∀ j, j < 11 → f j < 2 ^ 11) : ∀ n, n ≤ 11 →
    PackFld.Fld 11 (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc (fun s => Nat.lor s (Nat.shiftLeft (f j) (Nat.mul (nat_lit 11) j))))
      n) (fun i => if i < n then f i else 0)
  | 0, _ => PackFld.fld_congr (PackFld.fld_zero 11) (fun i => by simp)
  | n + 1, h => by
    change PackFld.Fld 11 (strictN _ _) _
    rw [sN_p]
    refine PackFld.fld_congr (PackFld.fld_or (fld_packR_p f hf n (by omega))
      (PackFld.fld_shl n (PackFld.fld_one (hf n (by omega))))) (fun i => ?_)
    by_cases h1 : i < n
    · have h2 : ¬ n ≤ i := by omega
      simp [h1, h2, show i < n + 1 by omega]
    · by_cases h3 : i = n
      · subst h3
        simp
      · have h4 : ¬ i < n + 1 := by omega
        have h5 : i - n ≠ 0 := by omega
        simp [h1, h4, h5]

theorem unpack11_packK_p (f : Nat → Nat) (hf : ∀ j, j < 11 → f j < 2 ^ 11) :
    unpack11 (packK f) = Array.ofFn (n := 11) fun j => f j.val := by
  refine Array.ext (by simp [unpack11, unpackW]) (fun j h1 h2 => ?_)
  have hj : j < 11 := by simpa [unpack11, unpackW] using h1
  simp only [unpack11, unpackW, Array.getElem_ofFn]
  change pg 11 (mask 11) (packK f) j = f j
  have := PackFld.pg_of_fld (fld_packR_p f hf 11 le_rfl) (i := j) (by simpa [hj] using hf j hj)
  simp only [hj, ↓reduceIte] at this
  exact this

theorem poly_sound {QP : Nat → Nat} (hQP : ∀ i < 11, powCols q23Cols i = unpack11 (QP i))
    {w R : Nat} (h : Nat.beq (packK fun i => appK (QP i) w) R = true) :
    polyCols w = unpack11 R := by
  rw [← Nat.eq_of_beq_eq_true h, unpack11_packK_p _ (fun j _ => appK_lt_p _ _), polyCols]
  refine Array.ext (by simp) (fun j h1 _ => ?_)
  have hj : j < 11 := by simpa using h1
  simp only [Array.getElem_ofFn]
  rw [hQP j hj, app_eq]

end CFSG.KS.SporSch.C11

end
