module

public import CFSG.GH74.QTGen4.Recog.G23.HSL
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.GH74.QTGen4.Recog.G23

theorem card_image_mul_two_le {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (h : ∀ y ∈ s.image f, 2 ≤ (s.filter fun x => f x = y).card) :
    2 * (s.image f).card ≤ s.card := by
  rw [Finset.card_eq_sum_card_image f s]
  calc 2 * (s.image f).card = ∑ _y ∈ s.image f, 2 := by simp [mul_comm]
    _ ≤ ∑ y ∈ s.image f, (s.filter fun x => f x = y).card := Finset.sum_le_sum h

theorem card_sq_pairs : (Finset.univ.filter (fun p : M2 × M2 => p.1.det = 1 ∧ p.2.det = 1 ∧
    ((p.1 * p.1 = 1 ∧ p.2 * p.2 = 1) ∨ (p.1 * p.1 = -1 ∧ p.2 * p.2 = -1)))).card = 40 := by
  decide +kernel

end CFSG.GH74.QTGen4.Recog.G23
