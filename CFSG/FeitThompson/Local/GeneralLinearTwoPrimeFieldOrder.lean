module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

theorem card_GL_one_zmod : Nat.card (GL (Fin 1) (ZMod p)) = p - 1 := by
  have := Matrix.card_GL_field (𝔽 := ZMod p) 1
  simpa [ZMod.card] using this

theorem card_GL_two_zmod : Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  have := Matrix.card_GL_field (𝔽 := ZMod p) 2
  simp [ZMod.card, Fin.prod_univ_two] at this
  simpa using this

theorem card_GL_two_zmod_factored :
    Nat.card (GL (Fin 2) (ZMod p)) = p * (p - 1) ^ 2 * (p + 1) := by
  rw [card_GL_two_zmod]
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by have := hp.out.two_le; omega⟩
  have hsq : (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
  have h1 : (a + 1) ^ 2 - 1 = a ^ 2 + 2 * a := by omega
  have h2 : (a + 1) ^ 2 - (a + 1) = a ^ 2 + a := by omega
  rw [h1, h2]
  simp only [Nat.add_sub_cancel]
  ring

private theorem cofactor_ne_zero : (p - 1) ^ 2 * (p + 1) ≠ 0 := by
  have h2 := hp.out.two_le
  have : p - 1 ≠ 0 := by omega
  positivity

private theorem not_dvd_cofactor : ¬ p ∣ (p - 1) ^ 2 * (p + 1) := by
  have h2 := hp.out.two_le
  intro h
  rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
  · have := Nat.le_of_dvd (by omega) (hp.out.dvd_of_dvd_pow h)
    omega
  · have h1 : p ∣ 1 := (Nat.dvd_add_right dvd_rfl).1 h
    have := Nat.le_of_dvd one_pos h1
    omega

theorem card_GL_two_zmod_ne_zero : Nat.card (GL (Fin 2) (ZMod p)) ≠ 0 := by
  have h2 := hp.out.two_le
  rw [card_GL_two_zmod_factored, mul_assoc]
  exact Nat.mul_ne_zero (by omega) (cofactor_ne_zero p)

theorem factorization_card_GL_two_zmod :
    (Nat.card (GL (Fin 2) (ZMod p))).factorization p = 1 := by
  have h2 := hp.out.two_le
  rw [card_GL_two_zmod_factored, mul_assoc, Nat.factorization_mul (by omega)
    (cofactor_ne_zero p), Finsupp.add_apply, Nat.Prime.factorization_self hp.out,
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_cofactor p)]

theorem pow_dvd_card_GL_two_zmod_iff {k : ℕ} :
    p ^ k ∣ Nat.card (GL (Fin 2) (ZMod p)) ↔ k ≤ 1 := by
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp.out (card_GL_two_zmod_ne_zero p),
    factorization_card_GL_two_zmod]

end CFSG.FeitThompson
