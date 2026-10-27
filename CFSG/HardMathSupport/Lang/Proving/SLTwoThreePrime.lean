module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.HardMathSupport.Lang.Proving

open Matrix

theorem transvection_pow_eq_smul {F : Type*} [Field F] {i j : Fin 2} (hij : i ≠ j) (b : F)
    (n : ℕ) :
    (SpecialLinearGroup.transvection hij b) ^ n = SpecialLinearGroup.transvection hij ((n : F) * b) := by
  induction n with
  | zero =>
    have h0 : SpecialLinearGroup.transvection hij (0 : F) = 1 := by
      apply Subtype.ext
      simp
    simp [h0]
  | succ n ih =>
    rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add]
    congr 1
    push_cast
    ring

theorem closure_pow_char_eq_one_eq_top {k : Type*} [Field k] [Finite k] {p : ℕ} [Fact p.Prime]
    [CharP k p] :
    Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin 2) k | g ^ p = 1} = ⊤ := by
  rw [eq_top_iff]
  intro A _
  refine SL2.transvection_induction (fun B => B ∈ Subgroup.closure
    {g : Matrix.SpecialLinearGroup (Fin 2) k | g ^ p = 1}) ?_ ?_ A
  · intro i j hij c
    apply Subgroup.subset_closure
    show (SpecialLinearGroup.transvection hij c) ^ p = 1
    rw [transvection_pow_eq_smul]
    have hp : ((p : k) * c) = 0 := by simp
    rw [hp]
    apply Subtype.ext
    simp
  · intro B C hB hC
    exact Subgroup.mul_mem _ hB hC

theorem three_dvd_card_specialLinearGroup_two {k : Type*} [Field k] [Finite k] :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
  have : Fintype k := Fintype.ofFinite k
  have hq2 : 2 ≤ Fintype.card k := Fintype.one_lt_card
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card k = m + 2 := ⟨Fintype.card k - 2, by omega⟩
  have hkcard : Nat.card k = m + 2 := by rw [Nat.card_eq_fintype_card, hm]
  have key := Matrix.card_SL_mul_card_units (n := Fin 2) (R := k)
  have hU : Nat.card kˣ = m + 1 := by rw [Nat.card_units, hkcard]; omega
  have hGL : Nat.card (GL (Fin 2) k) = ((m + 2) ^ 2 - 1) * ((m + 2) ^ 2 - (m + 2)) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, hm]
    simp
  have e1 : (m + 2) ^ 2 - 1 = (m + 1) * (m + 3) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (m + 2) ^ 2 - (m + 2) = (m + 2) * (m + 1) := Nat.sub_eq_of_eq_add (by ring)
  rw [hU, hGL, e1, e2] at key
  have hN : Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) = (m + 1) * (m + 2) * (m + 3) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < m + 1 by omega)
    rw [key]
    ring
  rw [hN]
  apply Nat.dvd_of_mod_eq_zero
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h <;>
    simp [Nat.mul_mod, Nat.add_mod, h]

end CFSG.HardMathSupport.Lang.Proving

end
