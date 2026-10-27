module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem arith_P (q₁ p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ q₁) (hlt : p < q₁)
    (h9 : q₁ ≤ 9) (hmod : q₁ % 4 = p % 4)
    (hv : ∀ k : ℕ, 2 ^ k ∣ q₁ ^ 2 - 1 ↔ 2 ^ k ∣ p ^ 2 - 1) (hnp : ¬ ∃ m, q₁ = p ^ m) : False := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h3 := hv 3
  have h4 := hv 4
  interval_cases q₁ <;> interval_cases p <;>
    first | omega | (exact absurd hp (by decide))

end CFSG.GH74.GLS.Stage4.Rest
