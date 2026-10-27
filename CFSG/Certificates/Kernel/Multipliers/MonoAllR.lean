module

public import Certificates.Data.Kernel.Multipliers.Mono

public section

namespace CFSG.Certificates.Mono

open CFSG.KC.Mono

theorem allR_succ (lo n : Nat) (p : Nat → Bool) :
    allR lo (n + 1) p = (p (lo + n) && allR lo n p) := by
  change CFSG.KC.andB (p (Nat.add lo n)) (allR lo n p) = _
  cases p (Nat.add lo n) <;> rfl

theorem allR_spec {lo n : Nat} {p : Nat → Bool} (h : allR lo n p = true) :
    ∀ x, lo ≤ x → x < lo + n → p x = true := by
  induction n with
  | zero => intro x h1 h2; omega
  | succ n ih =>
    rw [allR_succ, Bool.and_eq_true] at h
    intro x h1 h2
    rcases Nat.lt_or_ge x (lo + n) with h3 | h3
    · exact ih h.2 x h1 h3
    · have : x = lo + n := by omega
      subst this
      exact h.1

end CFSG.Certificates.Mono

end
