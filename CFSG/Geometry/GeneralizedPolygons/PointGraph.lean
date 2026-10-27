module

public import CFSG.Geometry.GeneralizedPolygons.Basic
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Geometry.GeneralizedPolygons

open SimpleGraph Matrix IsGeneralizedPolygon

universe u

variable {V : Type u} {G : SimpleGraph V} {m : ℕ} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

abbrev Points (c : G.Coloring (Fin 2)) : Type u := {v : V // c v = 0}

namespace IsGeneralizedPolygon

variable (hG : IsGeneralizedPolygon G m)
include hG

omit [DecidableEq V] in
theorem exists_point (hm : 2 ≤ m) (hthick : IsThick G) (c : G.Coloring (Fin 2)) :
    Nonempty (Points c) := by
  have hne : Nonempty V := by
    have := nontrivial_of_diam_ne_zero (G := G) (by rw [hG.diam_eq]; omega)
    infer_instance
  obtain ⟨v₀⟩ := hne
  have h3 := hthick v₀
  obtain ⟨v₁, hv₁⟩ := Finset.card_pos.1
    (show 0 < (G.neighborFinset v₀).card by rw [card_neighborFinset_eq_degree]; omega)
  rw [mem_neighborFinset] at hv₁
  have key : ∀ a b : Fin 2, a ≠ b → a = 0 ∨ b = 0 := by decide
  rcases key _ _ (c.valid hv₁) with h | h
  · exact ⟨⟨v₀, h⟩⟩
  · exact ⟨⟨v₁, h⟩⟩

end IsGeneralizedPolygon

end CFSG.Geometry.GeneralizedPolygons
