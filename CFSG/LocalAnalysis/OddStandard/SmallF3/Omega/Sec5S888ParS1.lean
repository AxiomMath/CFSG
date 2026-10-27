module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem par_sl23_trans (a b : SL23) (ha : a * a = -1) (hb : b * b = -1) :
    ∃ k : SL23, k * a * k⁻¹ = b ∨ k * a * k⁻¹ = -b :=
  (by decide +kernel : ∀ a b : SL23, a * a = -1 → b * b = -1 →
    ∃ k : SL23, k * a * k⁻¹ = b ∨ k * a * k⁻¹ = -b) a b ha hb

theorem par_sl23_fixfree (k a : SL23) (ha : a * a = -1) (hk : k ^ 4 ≠ 1) :
    k * a * k⁻¹ ≠ a ∧ k * a * k⁻¹ ≠ -a :=
  (by decide +kernel : ∀ k a : SL23, a * a = -1 → k ^ 4 ≠ 1 →
    k * a * k⁻¹ ≠ a ∧ k * a * k⁻¹ ≠ -a) k a ha hk

theorem par_sl23_sq_not_q8 (k : SL23) (hk : k ^ 4 ≠ 1) : (k * k) ^ 4 ≠ 1 :=
  (by decide +kernel : ∀ k : SL23, k ^ 4 ≠ 1 → (k * k) ^ 4 ≠ 1) k hk

theorem par_sl23_kernel (x : SL23)
    (h : ∀ q : SL23, q ^ 4 = 1 → x * q * x⁻¹ = q ∨ x * q * x⁻¹ = -q) : x ^ 4 = 1 :=
  (by decide +kernel : ∀ x : SL23, (∀ q : SL23, q ^ 4 = 1 → x * q * x⁻¹ = q ∨
    x * q * x⁻¹ = -q) → x ^ 4 = 1) x h

theorem par_sl23_q8_mod (x q : SL23) (hx : x ^ 4 = 1) (hq : q ^ 4 = 1) :
    x * q * x⁻¹ = q ∨ x * q * x⁻¹ = -q :=
  (by decide +kernel : ∀ x q : SL23, x ^ 4 = 1 → q ^ 4 = 1 →
    x * q * x⁻¹ = q ∨ x * q * x⁻¹ = -q) x q hx hq

theorem par_sl23_card_sq : Nat.card {x : SL23 // x * x = -1} = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem par_sl23_decomp (a b x : SL23) (ha : a * a = -1) (hb : b * b = -1) (hba : b ≠ a)
    (hba' : b ≠ -a) (hx : x ^ 4 = 1) :
    x = 1 ∨ x = -1 ∨ x = a ∨ x = -a ∨ x = b ∨ x = -b ∨ x = a * b ∨ x = -(a * b) :=
  by
  have h : x ∈ ({1, -1, a, -a, b, -b, a * b, -(a * b)} : Finset SL23) :=
    (by decide +kernel : ∀ a b x : SL23, a * a = -1 → b * b = -1 → b ≠ a → b ≠ -a →
      x ^ 4 = 1 → x ∈ ({1, -1, a, -a, b, -b, a * b, -(a * b)} : Finset SL23))
      a b x ha hb hba hba' hx
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

theorem par_sl23_exists_other (a : SL23) (ha : a * a = -1) :
    ∃ b : SL23, b * b = -1 ∧ b ≠ a ∧ b ≠ -a :=
  (by decide +kernel : ∀ a : SL23, a * a = -1 → ∃ b : SL23, b * b = -1 ∧ b ≠ a ∧ b ≠ -a) a ha

theorem par_sl23_anticomm (a b : SL23) (ha : a * a = -1) (hb : b * b = -1) (hba : b ≠ a)
    (hba' : b ≠ -a) : b * a = -(a * b) :=
  (by decide +kernel : ∀ a b : SL23, a * a = -1 → b * b = -1 → b ≠ a → b ≠ -a →
    b * a = -(a * b)) a b ha hb hba hba'

end CFSG.OddStandard.SmallF3.Omega
