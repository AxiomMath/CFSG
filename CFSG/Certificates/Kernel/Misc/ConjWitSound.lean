module

public import Certificates.Data.Kernel.Misc.ConjWit

public section

namespace CFSG.KC.Misc.ConjWit

open CFSG.KC.Enum (pcomp)
open CFSG.KS (mask)

variable {n w S B NH NT : Nat} {H TT P : Nat → Nat} {Z0 Z1 Z2 : Nat}

theorem witL_spec : ∀ (W : List Nat) (i : Nat),
    witL n w S B NH NT H TT P Z0 Z1 Z2 W i = true →
      ∀ j < W.length, witK n w S B NH NT H TT Z0 Z1 Z2 (P (i + j)) W[j]! = true
  | [], _, _, j, hj => absurd hj (by simp)
  | a :: W, i, h, j, hj => by
    have e : witL n w S B NH NT H TT P Z0 Z1 Z2 (a :: W) i =
        (witK n w S B NH NT H TT Z0 Z1 Z2 (P i) a &&
          witL n w S B NH NT H TT P Z0 Z1 Z2 W (Nat.add i 1)) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases j with _ | j
    · simpa using h.1
    · have := witL_spec W (Nat.add i 1) h.2 j (by simpa using hj)
      rw [List.getElem!_cons_succ]
      have e2 : Nat.add i 1 + j = i + (j + 1) := by simp only [Nat.add_eq]; omega
      rwa [e2] at this

theorem witK_spec {s wit : Nat} (h : witK n w S B NH NT H TT Z0 Z1 Z2 s wit = true) :
    (s = Z0 ∨ s = Z1 ∨ s = Z2) ∨
      (wit % B < NH ∧ wit / B < NT ∧
        pcomp n w (mask w) (H (wit % B)) s = pcomp n w (mask w) (TT (wit / B)) (H (wit % B))) := by
  unfold witK at h
  cases hb : Nat.blt wit S
  · rw [hb] at h
    simp only [Bool.or_eq_true] at h
    left
    rcases h with (h | h) | h
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
    · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h))
    · exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h))
  · rw [hb] at h
    simp only [cwE, Bool.and_eq_true, Nat.blt_eq] at h
    right
    exact ⟨h.1.1, h.1.2, Nat.eq_of_beq_eq_true h.2⟩

end CFSG.KC.Misc.ConjWit

end
