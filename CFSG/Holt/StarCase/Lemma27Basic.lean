module

public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Holt

open MulAction CFSG.Open
open scoped Pointwise

namespace StarLemma27

section Lift

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem smul_eq_of_odd_orderOf {x : G} (hx : Odd (orderOf x)) {a b : Ω} (hab : a ≠ b)
    (ha : x • a = a ∨ x • a = b) (hb : x • b = a ∨ x • b = b) : x • a = a := by
  rcases ha with ha | ha
  · exact ha
  exfalso
  have hb' : x • b = a := hb.resolve_right fun h => hab (smul_left_cancel x (ha.trans h.symm))
  have h2 : ∀ k : ℕ, x ^ (2 * k + 1) • a = b := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih => rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by ring, pow_add, mul_smul, ih,
        sq, mul_smul, hb', ha]
  obtain ⟨k, hk⟩ := hx
  have := h2 k
  rw [← hk, pow_orderOf_eq_one, one_smul] at this
  exact hab this

end Lift

end StarLemma27

end CFSG.Holt
