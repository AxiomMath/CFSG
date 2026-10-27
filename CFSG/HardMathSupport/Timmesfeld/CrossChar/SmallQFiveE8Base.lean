module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open scoped Matrix

@[expose] def e5Rows : List (List ℤ) :=
  [[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 3, 3, 0], [0, 1, 0, 2, 0, 0, 4, 2],
    [1, 0, 0, 3, 0, 0, 4, 0]]

@[expose] def E5 (i : Fin 4) : Fin 8 → ZMod 5 :=
  fun j => (((e5Rows.getD i []).getD j 0 : ℤ) : ZMod 5)

@[expose] def xc (c : Fin 4 → ZMod 5) : Fin 8 → ZMod 5 :=
  fun j => ∑ i, c i * E5 i j

theorem xc_add (c d : Fin 4 → ZMod 5) : xc (c + d) = xc c + xc d := by
  funext j
  simp only [xc, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem xc_zero : xc 0 = 0 := by
  funext j
  simp [xc]

theorem xc_pivots (c : Fin 4 → ZMod 5) :
    xc c 4 = c 0 ∧ xc c 2 = c 1 ∧ xc c 1 = c 2 ∧ xc c 0 = c 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [xc, E5, e5Rows, Fin.sum_univ_four]

theorem xc_injective : Function.Injective xc := by
  intro c d h
  have h4 := (xc_pivots c).1
  have h2 := (xc_pivots c).2.1
  have h1 := (xc_pivots c).2.2.1
  have h0 := (xc_pivots c).2.2.2
  have h4' := (xc_pivots d).1
  have h2' := (xc_pivots d).2.1
  have h1' := (xc_pivots d).2.2.1
  have h0' := (xc_pivots d).2.2.2
  rw [h] at h4 h2 h1 h0
  funext i
  fin_cases i
  · exact h4.symm.trans h4'
  · exact h2.symm.trans h2'
  · exact h1.symm.trans h1'
  · exact h0.symm.trans h0'

@[expose] def e8MTab : Fin 8 → Fin 8 → ℤ :=
  ![![-2, 0, 0, 0, 1, 0, 0, 0], ![-3, 0, 0, 0, 1, 0, 1, -1], ![-4, 0, 0, 0, 1, 1, 0, 0],
    ![-6, 0, 0, 0, 2, 0, 1, 0], ![-5, 0, 0, 0, 2, 0, 0, 0], ![-3, 0, -1, 0, 2, 0, 0, 0],
    ![-2, 0, 0, -1, 2, 0, 0, 0], ![-1, 1, 0, -1, 1, 0, 0, 0]]

theorem eig_eq_xc_aux {x : Fin 8 → ZMod 5}
    (hx : ∀ j : Fin 8, ∑ k, x k * ((e8MTab k j : ℤ) : ZMod 5) = 2 * x j) :
    x = xc ![x 4, x 2, x 1, x 0] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : ZMod 5,
      x = ![a0, a1, a2, a3, a4, a5, a6, a7] :=
    ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, by funext j; fin_cases j <;> rfl⟩
  have hc5 : (5 : ZMod 5) = 0 := rfl
  have e0 := hx 0
  have e1 := hx 1
  have e2 := hx 2
  have e3 := hx 3
  have e4 := hx 4
  have e5 := hx 5
  have e6 := hx 6
  have e7 := hx 7
  simp [Fin.sum_univ_eight, e8MTab] at e0 e1 e2 e3 e4 e5 e6 e7
  have f5 : a5 = 3 * a2 := by
    linear_combination (2 : ZMod 5) * e5 + (-((1 : ZMod 5) * a2 + (-1 : ZMod 5) * a5)) * hc5
  have f7 : a7 = 2 * a1 := by
    linear_combination (2 : ZMod 5) * e7 + (-((-1 : ZMod 5) * a7)) * hc5
  have f3 : a3 = a2 + 2 * a1 + 3 * a0 := by
    linear_combination (2 : ZMod 5) * e4 + (2 : ZMod 5) * e5 + (2 : ZMod 5) * e6 +
      (1 : ZMod 5) * e7 + (-((1 : ZMod 5) * a0 + (1 : ZMod 5) * a1 + (1 : ZMod 5) * a2 +
        (1 : ZMod 5) * a3)) * hc5
  have f6 : a6 = 3 * a2 + 4 * a1 + 4 * a0 := by
    linear_combination (1 : ZMod 5) * e4 + (1 : ZMod 5) * e5 + (3 : ZMod 5) * e6 +
      (3 : ZMod 5) * e7 + (-((1 : ZMod 5) * a0 + (1 : ZMod 5) * a1 + (1 : ZMod 5) * a2 +
        (1 : ZMod 5) * a3 + (-1 : ZMod 5) * a6 + (-1 : ZMod 5) * a7)) * hc5
  funext j
  fin_cases j <;> simp [xc, E5, e5Rows, Fin.sum_univ_four, f5, f7, f3, f6] <;> ring

theorem sl2_eq_one_of_central_charTwo {F : Type} [Field F] [CharP F 2]
    {X : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : ∀ Z : Matrix.SpecialLinearGroup (Fin 2) F, X * Z = Z * X) : X = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, b, c, d, hX⟩ : ∃ a b c d : F, (X : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  let U : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  let V : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  have hu : (X : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] * (X : Matrix (Fin 2) (Fin 2) F) := congrArg Subtype.val (h U)
  have hv : (X : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] =
      !![1, 0; 1, 1] * (X : Matrix (Fin 2) (Fin 2) F) := congrArg Subtype.val (h V)
  rw [hX] at hu hv
  have hu00 : a = a + c := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hu 0) 0
  have hu01 : a + b = b + d := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hu 0) 1
  have hv00 : a + b = a := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hv 0) 0
  have hdet : a * d - b * c = 1 := by
    have := X.2
    rw [hX, Matrix.det_fin_two_of] at this
    exact this
  have hc : c = 0 := by linear_combination -hu00
  have hb : b = 0 := by linear_combination hv00
  have had : d = a := by linear_combination -hu01
  rw [hb, hc, had] at hdet
  have ha : a = 1 := by
    have : (a - 1) * (a - 1) = 0 := by linear_combination hdet + (1 - a) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  apply Subtype.ext
  rw [hX, hb, hc, had, ha]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def pairZ (x : Fin 8 → ZMod 5) (v : Fin 8 → ℤ) : ZMod 5 :=
  ∑ i, x i * ((v i : ℤ) : ZMod 5)

theorem pairZ_single (x : Fin 8 → ZMod 5) (j : Fin 8) :
    pairZ x (Pi.single j 1) = x j := by
  simp [pairZ, Pi.single_apply]

theorem sum_mul_single (f : Fin 8 → ZMod 5) (j : Fin 8) :
    ∑ j', f j' * (((Pi.single j (1 : ℤ) : Fin 8 → ℤ) j' : ℤ) : ZMod 5) = f j := by
  simp [Pi.single_apply]

@[expose] def rrv (v : Fin 8 → ℤ) : Fin 4 → ZMod 5 := fun i => pairZ (E5 i) v

theorem pairZ_xc (c : Fin 4 → ZMod 5) (v : Fin 8 → ℤ) :
    pairZ (xc c) v = c ⬝ᵥ rrv v := by
  simp only [pairZ, xc, rrv, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end
