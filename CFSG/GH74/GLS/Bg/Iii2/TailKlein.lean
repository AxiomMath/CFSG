module

public import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Tauto

public section

namespace CFSG.GH74.GLS.Bg.Iii2

variable {G : Type} [Group G]

theorem klein_swap {a b x y : G} (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a)
    (hx : x = a ∨ x = b ∨ x = a * b) (hy : y = a ∨ y = b ∨ y = a * b) (hxy : x ≠ y) :
    ∀ w, (w = a ∨ w = b ∨ w = a * b) → (w = x ∨ w = y ∨ w = x * y) := by
  have h1 : a * (a * b) = b := by rw [← mul_assoc, haa, one_mul]
  have h2 : a * b * a = b := by rw [hab, mul_assoc, haa, mul_one]
  have h3 : b * (a * b) = a := by rw [hab, ← mul_assoc, hbb, one_mul]
  have h4 : a * b * b = a := by rw [mul_assoc, hbb, mul_one]
  intro w hw
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hxy ⊢ <;>
  first
  | exact absurd rfl hxy
  | ((try simp only [h1, h2, h3, h4, ← hab]); tauto)

end CFSG.GH74.GLS.Bg.Iii2
