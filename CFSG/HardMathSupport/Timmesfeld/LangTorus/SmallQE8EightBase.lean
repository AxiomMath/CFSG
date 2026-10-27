module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

open scoped Matrix

@[expose] def e17Rows : List (List ℤ) :=
  [[3, 4, 6, 13, 2, 9, 1, 0], [2, 16, 4, 8, 2, 15, 0, 1]]

@[expose] def E17 (i : Fin 2) : Fin 8 → ZMod 17 :=
  fun j => (((e17Rows.getD i []).getD j 0 : ℤ) : ZMod 17)

@[expose] def xc17 (c : Fin 2 → ZMod 17) : Fin 8 → ZMod 17 :=
  fun j => ∑ i, c i * E17 i j

theorem xc17_add (c d : Fin 2 → ZMod 17) : xc17 (c + d) = xc17 c + xc17 d := by
  funext j
  simp only [xc17, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem xc17_zero : xc17 0 = 0 := by
  funext j
  simp [xc17]

theorem xc17_pivots (c : Fin 2 → ZMod 17) : xc17 c 6 = c 0 ∧ xc17 c 7 = c 1 := by
  refine ⟨?_, ?_⟩ <;>
  · simp [xc17, E17, e17Rows, Fin.sum_univ_two]

theorem xc17_injective : Function.Injective xc17 := by
  intro c d h
  have h6 := (xc17_pivots c).1
  have h7 := (xc17_pivots c).2
  have h6' := (xc17_pivots d).1
  have h7' := (xc17_pivots d).2
  rw [h] at h6 h7
  funext i
  fin_cases i
  · exact h6.symm.trans h6'
  · exact h7.symm.trans h7'

@[expose] def e8MTab17 : Fin 8 → Fin 8 → ℤ :=
  ![![0, 2, 0, -1, 0, 0, 1, -1], ![0, 2, 1, -2, 1, -1, 2, -2], ![1, 3, 0, -2, 1, -1, 2, -2],
    ![0, 4, 1, -3, 2, -2, 3, -3], ![0, 3, 1, -2, 1, -2, 3, -2], ![0, 2, 1, -1, 0, -1, 2, -2],
    ![0, 2, 1, -1, 0, -1, 1, -1], ![0, 1, 1, -1, 0, 0, 0, 0]]

theorem eig_eq_xc17_aux {x : Fin 8 → ZMod 17}
    (hx : ∀ j : Fin 8, ∑ k, x k * ((e8MTab17 k j : ℤ) : ZMod 17) = 2 * x j) :
    x = xc17 ![x 6, x 7] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : ZMod 17,
      x = ![a0, a1, a2, a3, a4, a5, a6, a7] :=
    ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, by funext j; fin_cases j <;> rfl⟩
  have hc17 : (17 : ZMod 17) = 0 := rfl
  have e0 : a0 * (0 : ZMod 17) + a1 * (0 : ZMod 17) + a2 * (1 : ZMod 17) + a3 * (0 : ZMod 17) +
      a4 * (0 : ZMod 17) + a5 * (0 : ZMod 17) + a6 * (0 : ZMod 17) + a7 * (0 : ZMod 17) =
      2 * a0 := by
    simpa [Fin.sum_univ_eight, e8MTab17] using hx 0
  have e1 : a0 * (2 : ZMod 17) + a1 * (2 : ZMod 17) + a2 * (3 : ZMod 17) + a3 * (4 : ZMod 17) +
      a4 * (3 : ZMod 17) + a5 * (2 : ZMod 17) + a6 * (2 : ZMod 17) + a7 * (1 : ZMod 17) =
      2 * a1 := by
    simpa [Fin.sum_univ_eight, e8MTab17] using hx 1
  have e2 : a0 * (0 : ZMod 17) + a1 * (1 : ZMod 17) + a2 * (0 : ZMod 17) + a3 * (1 : ZMod 17) +
      a4 * (1 : ZMod 17) + a5 * (1 : ZMod 17) + a6 * (1 : ZMod 17) + a7 * (1 : ZMod 17) =
      2 * a2 := by
    simpa [Fin.sum_univ_eight, e8MTab17] using hx 2
  have e3 : a0 * (-1 : ZMod 17) + a1 * (-2 : ZMod 17) + a2 * (-2 : ZMod 17) +
      a3 * (-3 : ZMod 17) + a4 * (-2 : ZMod 17) + a5 * (-1 : ZMod 17) + a6 * (-1 : ZMod 17) +
      a7 * (-1 : ZMod 17) = 2 * a3 := by
    simpa [Fin.sum_univ_eight, e8MTab17] using hx 3
  have e4 : a0 * (0 : ZMod 17) + a1 * (1 : ZMod 17) + a2 * (1 : ZMod 17) + a3 * (2 : ZMod 17) +
      a4 * (1 : ZMod 17) + a5 * (0 : ZMod 17) + a6 * (0 : ZMod 17) + a7 * (0 : ZMod 17) =
      2 * a4 := by
    simpa [Fin.sum_univ_eight, e8MTab17] using hx 4
  have e5 : a0 * (0 : ZMod 17) + a1 * (-1 : ZMod 17) + a2 * (-1 : ZMod 17) +
      a3 * (-2 : ZMod 17) + a4 * (-2 : ZMod 17) + a5 * (-1 : ZMod 17) + a6 * (-1 : ZMod 17) +
      a7 * (0 : ZMod 17) = 2 * a5 := by
    simpa [Fin.sum_univ_eight, e8MTab17] using hx 5
  have f0 : a0 = (3 : ZMod 17) * a6 + (2 : ZMod 17) * a7 := by
    linear_combination (6 : ZMod 17) * e0 + (6 : ZMod 17) * e1 + (8 : ZMod 17) * e2 +
      (16 : ZMod 17) * e3 + (14 : ZMod 17) * e4 + (7 : ZMod 17) * e5 +
      ((1 : ZMod 17) * a0 + (1 : ZMod 17) * a1 + (1 : ZMod 17) * a2 + (2 : ZMod 17) * a3 +
        (2 : ZMod 17) * a4 + (1 : ZMod 17) * a5) * hc17
  have f1 : a1 = (4 : ZMod 17) * a6 + (16 : ZMod 17) * a7 := by
    linear_combination (10 : ZMod 17) * e0 + (10 : ZMod 17) * e1 + (8 : ZMod 17) * e2 +
      (8 : ZMod 17) * e4 + (15 : ZMod 17) * e5 +
      ((-1 : ZMod 17) * a2 + (-2 : ZMod 17) * a3 + (1 : ZMod 17) * a5 + (-1 : ZMod 17) * a6 +
        (-2 : ZMod 17) * a7) * hc17
  have f2 : a2 = (6 : ZMod 17) * a6 + (4 : ZMod 17) * a7 := by
    linear_combination (13 : ZMod 17) * e0 + (12 : ZMod 17) * e1 + (16 : ZMod 17) * e2 +
      (15 : ZMod 17) * e3 + (11 : ZMod 17) * e4 + (14 : ZMod 17) * e5 +
      ((1 : ZMod 17) * a0 + (1 : ZMod 17) * a1 + (1 : ZMod 17) * a2 + (1 : ZMod 17) * a3 +
        (1 : ZMod 17) * a4 + (1 : ZMod 17) * a5 + (-1 : ZMod 17) * a6 +
        (-1 : ZMod 17) * a7) * hc17
  have f3 : a3 = (13 : ZMod 17) * a6 + (8 : ZMod 17) * a7 := by
    linear_combination (16 : ZMod 17) * e0 + (14 : ZMod 17) * e1 + (8 : ZMod 17) * e2 +
      (13 : ZMod 17) * e3 + (3 : ZMod 17) * e4 + (2 : ZMod 17) * e5 +
      ((1 : ZMod 17) * a0 + (1 : ZMod 17) * a1 + (-1 : ZMod 17) * a2 + (-1 : ZMod 17) * a4 +
        (-1 : ZMod 17) * a5 + (-2 : ZMod 17) * a6 + (-1 : ZMod 17) * a7) * hc17
  have f4 : a4 = (2 : ZMod 17) * a6 + (2 : ZMod 17) * a7 := by
    linear_combination (4 : ZMod 17) * e0 + (16 : ZMod 17) * e1 + (6 : ZMod 17) * e2 +
      (7 : ZMod 17) * e3 + (7 : ZMod 17) * e4 + (16 : ZMod 17) * e5 +
      ((-1 : ZMod 17) * a0 + (1 : ZMod 17) * a1 + (-1 : ZMod 17) * a2 + (-1 : ZMod 17) * a3 +
        (1 : ZMod 17) * a5 + (-1 : ZMod 17) * a6 + (-1 : ZMod 17) * a7) * hc17
  have f5 : a5 = (9 : ZMod 17) * a6 + (15 : ZMod 17) * a7 := by
    linear_combination (13 : ZMod 17) * e0 + (1 : ZMod 17) * e1 + (11 : ZMod 17) * e2 +
      (10 : ZMod 17) * e3 + (4 : ZMod 17) * e4 + (12 : ZMod 17) * e5 +
      ((2 : ZMod 17) * a0 + (1 : ZMod 17) * a1 + (2 : ZMod 17) * a2 + (3 : ZMod 17) * a3 +
        (2 : ZMod 17) * a4 + (2 : ZMod 17) * a5 + (-1 : ZMod 17) * a7) * hc17
  funext j
  fin_cases j <;> simp [xc17, E17, e17Rows, Fin.sum_univ_two, f0, f1, f2, f3, f4, f5] <;> ring

@[expose] def pairZ17 (x : Fin 8 → ZMod 17) (v : Fin 8 → ℤ) : ZMod 17 :=
  ∑ i, x i * ((v i : ℤ) : ZMod 17)

theorem pairZ17_single (x : Fin 8 → ZMod 17) (j : Fin 8) :
    pairZ17 x (Pi.single j 1) = x j := by
  simp [pairZ17, Pi.single_apply]

@[expose] def rrv17 (v : Fin 8 → ℤ) : Fin 2 → ZMod 17 := fun i => pairZ17 (E17 i) v

theorem pairZ17_xc (c : Fin 2 → ZMod 17) (v : Fin 8 → ℤ) :
    pairZ17 (xc17 c) v = c ⬝ᵥ rrv17 v := by
  simp only [pairZ17, xc17, rrv17, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eq_zero_of_dotProduct17 (r : Fin 2 → ZMod 17) (h : ∀ c : Fin 2 → ZMod 17, c ⬝ᵥ r = 0) :
    r = 0 := by
  funext i
  have := h (Pi.single i 1)
  simpa using this

theorem eq_of_dotProduct17 {r s : Fin 2 → ZMod 17}
    (h : ∀ c : Fin 2 → ZMod 17, c ⬝ᵥ r = c ⬝ᵥ s) : r = s := by
  funext i
  have := h (Pi.single i 1)
  simpa using this

theorem eq_one_of_conj_fixed {F : Type} [Field F] [CharP F 2] (t : F) (a b c d : F)
    (hdet : a * d - b * c = 1) (haa : a * a + b * c = 1) (hb : t * b = b) (hc : t⁻¹ * c = c) :
    t = 1 ∨ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) := by
  by_cases ht1 : t = 1
  · exact Or.inl ht1
  · right
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have hb0 : b = 0 := by
      have h : (t - 1) * b = 0 := by linear_combination hb
      rcases mul_eq_zero.1 h with h | h
      · exact absurd (sub_eq_zero.1 h) ht1
      · exact h
    have hc0 : c = 0 := by
      have h : (t⁻¹ - 1) * c = 0 := by linear_combination hc
      rcases mul_eq_zero.1 h with h | h
      · exact absurd (inv_eq_one.1 (sub_eq_zero.1 h)) ht1
      · exact h
    rw [hb0, hc0] at hdet haa
    have ha : a = 1 := by
      have h : (a - 1) * (a - 1) = 0 := by linear_combination haa + (1 - a) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 h)
    refine ⟨ha, hb0, hc0, ?_⟩
    rw [ha] at hdet
    linear_combination hdet

end CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

end
