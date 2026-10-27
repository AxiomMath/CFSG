module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddQuadratic

open QuadraticMap

variable {K : Type*} [Field K] [Finite K]

omit [Field K] [Finite K] in
theorem odd_card_mod_two (hodd : Odd (Nat.card K)) : Nat.card K % 2 = 1 := by
  exact Nat.odd_iff.mp hodd

theorem char_ne_two_of_odd_card (hodd : Odd (Nat.card K)) : ringChar K ≠ 2 := by
  let := Fintype.ofFinite K
  intro hchar
  have heven := FiniteField.even_card_of_char_two hchar
  rw [Fintype.card_eq_nat_card, odd_card_mod_two hodd] at heven
  exact Nat.one_ne_zero heven

theorem two_ne_zero_of_odd_card (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 :=
  Ring.two_ne_zero (char_ne_two_of_odd_card hodd)

theorem exists_weighted_ternary_zero (hodd : Odd (Nat.card K))
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (c : K) :
    ∃ x y : K, a * x ^ 2 + b * y ^ 2 + c = 0 := by
  let := Fintype.ofFinite K
  let f : Polynomial K := Polynomial.C a * Polynomial.X ^ 2
  let g : Polynomial K := Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C c
  have hf : f.degree = 2 := Polynomial.degree_C_mul_X_pow 2 ha
  have hg : g.degree = 2 := by
    rw [show g = Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C c from rfl,
      Polynomial.degree_add_C]
    · exact Polynomial.degree_C_mul_X_pow 2 hb
    · rw [Polynomial.degree_C_mul_X_pow 2 hb]
      decide
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (by simpa only [Fintype.card_eq_nat_card] using odd_card_mod_two hodd)
  refine ⟨x, y, ?_⟩
  simpa [f, g, add_assoc] using hxy

theorem weightedSumSquares_not_anisotropic (hodd : Odd (Nat.card K))
    {n : ℕ} (hn : 3 ≤ n) (w : Fin n → Kˣ) :
    ¬ (weightedSumSquares K w).Anisotropic := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  have hik : i ≠ k := by
    intro h
    have := congrArg Fin.val h
    simp [i, k] at this
  have hjk : j ≠ k := by
    intro h
    have := congrArg Fin.val h
    simp [j, k] at this
  obtain ⟨x, y, hxy⟩ := exists_weighted_ternary_zero hodd (w i).ne_zero (w j).ne_zero
    (w k : K)
  rw [weightedSumSquares_units]
  apply not_anisotropic_weightedSumSquares_of_ternary_eq_zero
    (fun l => (w l : K)) hij hik hjk (x := x) (y := y) (z := 1) one_ne_zero
  simpa using hxy

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_isotropic_of_three_le (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hV : 3 ≤ Module.finrank K V) : ∃ v : V, v ≠ 0 ∧ Q v = 0 := by
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_odd_card hodd)
  have hnd : Q.Nondegenerate := nondegenerate_polar_iff.mp hQ
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (nondegenerate_associated_iff.mpr hnd).1
  apply Q.not_anisotropic_iff_exists.mp
  intro haniso
  apply weightedSumSquares_not_anisotropic hodd hV w
  intro v hv
  apply e.symm.injective
  simpa using haniso (e.symm v) ((e.symm.map_app v).trans hv)

theorem anisotropic_finrank_le_two (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (haniso : Q.Anisotropic) :
    Module.finrank K V ≤ 2 := by
  by_contra! hdim
  obtain ⟨v, hv, hvQ⟩ := exists_isotropic_of_three_le hodd Q hQ (by omega)
  exact hv (haniso v hvQ)

end CFSG.ComponentClassification.CatalogueBOddQuadratic
