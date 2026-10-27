module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LinearGroups

theorem hua_field_identity {K : Type*} [Field K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a * b ≠ 1) :
    b⁻¹ - a ≠ 0 ∧ a⁻¹ + (b⁻¹ - a)⁻¹ ≠ 0 ∧ a - (a⁻¹ + (b⁻¹ - a)⁻¹)⁻¹ = a ^ 2 * b := by
  have h1 : 1 - a * b ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have e1 : b⁻¹ - a = (1 - a * b) / b := by field_simp
  have hb1 : b⁻¹ - a ≠ 0 := by rw [e1]; exact div_ne_zero h1 hb
  have e2 : a⁻¹ + (b⁻¹ - a)⁻¹ = (a * (1 - a * b))⁻¹ := by
    rw [e1, inv_div]
    field_simp
    ring
  have h2 : a⁻¹ + (b⁻¹ - a)⁻¹ ≠ 0 := by rw [e2]; exact inv_ne_zero (mul_ne_zero ha h1)
  refine ⟨hb1, h2, ?_⟩
  rw [e2, inv_inv]
  ring

end CFSG.LinearGroups
