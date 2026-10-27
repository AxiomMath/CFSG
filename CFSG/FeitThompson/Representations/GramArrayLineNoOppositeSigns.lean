module

public import Mathlib.Data.Matrix.Mul
import CFSG.FeitThompson.Representations.IntegerVectorSquaredLengthThree
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset Matrix

section Aux

variable {ι : Type*} [Fintype ι]

theorem eq_single_of_dotProduct_self_eq_sq [DecidableEq ι] {w : ι → ℤ} {a : ι}
    (hw : w ⬝ᵥ w = w a ^ 2) : w = Pi.single a (w a) := by
  have key : ∀ c, c ≠ a → w c = 0 := by
    intro c hc
    by_contra hne
    have h1 : w a ^ 2 + w c ^ 2 ≤ w ⬝ᵥ w := by
      rw [dotProduct]
      calc w a ^ 2 + w c ^ 2 = ∑ i ∈ ({a, c} : Finset ι), w i * w i := by
            rw [Finset.sum_pair (Ne.symm hc)]; ring
        _ ≤ ∑ i, w i * w i :=
            Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
              (fun i _ _ => mul_self_nonneg _)
    have h2 : (0 : ℤ) < w c ^ 2 := by positivity
    omega
  funext m
  by_cases hm : m = a
  · subst hm; simp
  · simp [hm, key m hm]

theorem mul_nonneg_of_dotProduct_eq_three_of_witness
    {u v z : ι → ℤ} (hu : u ⬝ᵥ u = 3) (hv : v ⬝ᵥ v = 3) (huv : u ⬝ᵥ v = 1)
    (hzu : z ⬝ᵥ u = 1) (hzv : z ⬝ᵥ v = 0) (a : ι) : 0 ≤ u a * v a := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hua : u a ≠ 0 := by rintro h; simp [h] at hlt
  have hva : v a ≠ 0 := by rintro h; simp [h] at hlt
  have hu1 := eq_one_or_neg_one_of_dotProduct_self_eq_three hu hua
  have hv1 := eq_one_or_neg_one_of_dotProduct_self_eq_three hv hva
  have hdiff : (u - v) a = 2 ∨ (u - v) a = -2 := by
    simp only [Pi.sub_apply]
    rcases hu1 with h1 | h1 <;> rcases hv1 with h2 | h2 <;> rw [h1, h2] at hlt ⊢ <;> omega
  have hvu : v ⬝ᵥ u = 1 := by rw [dotProduct_comm]; exact huv
  have hd4 : (u - v) ⬝ᵥ (u - v) = 4 := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hu, hv, huv, hvu]; norm_num
  have hsq : (u - v) ⬝ᵥ (u - v) = ((u - v) a) ^ 2 := by
    rw [hd4]; rcases hdiff with h | h <;> rw [h] <;> norm_num
  have h1 : z ⬝ᵥ (u - v) = 1 := by rw [dotProduct_sub, hzu, hzv]; ring
  rw [eq_single_of_dotProduct_self_eq_sq hsq, dotProduct_single] at h1
  rcases hdiff with h | h <;> rw [h] at h1 <;> omega

end Aux

variable {μ ν ι : Type*} [DecidableEq μ] [DecidableEq ν] [Fintype ι]

def IsGramArray (b : μ → ν → ι → ℤ) : Prop :=
  ∀ i j k l, b i j ⬝ᵥ b k l =
    (if i = k then 1 else 0) + (if j = l then 1 else 0) +
      (if i = k then 1 else 0) * (if j = l then 1 else 0)

namespace IsGramArray

variable {b : μ → ν → ι → ℤ} (hb : IsGramArray b)
include hb

theorem dotProduct_eq (i : μ) (j : ν) (k : μ) (l : ν) :
    b i j ⬝ᵥ b k l = (if i = k then 1 else 0) + (if j = l then 1 else 0) +
      (if i = k then 1 else 0) * (if j = l then 1 else 0) := hb i j k l

theorem dotProduct_self (i : μ) (j : ν) : b i j ⬝ᵥ b i j = 3 := by
  simpa using hb i j i j

theorem dotProduct_row (i : μ) {j l : ν} (hjl : j ≠ l) : b i j ⬝ᵥ b i l = 1 := by
  simpa [hjl] using hb i j i l

theorem dotProduct_col {i k : μ} (hik : i ≠ k) (j : ν) : b i j ⬝ᵥ b k j = 1 := by
  simpa [hik] using hb i j k j

theorem dotProduct_eq_zero {i k : μ} {j l : ν} (hik : i ≠ k) (hjl : j ≠ l) :
    b i j ⬝ᵥ b k l = 0 := by
  simpa [hik, hjl] using hb i j k l

theorem transpose : IsGramArray (fun j i => b i j) := by
  intro j i l k
  rw [hb i j k l]
  ring

end IsGramArray

theorem isGramArray_of_dotProduct {b : μ → ν → ι → ℤ}
    (hself : ∀ i j, b i j ⬝ᵥ b i j = 3)
    (hrow : ∀ i, ∀ {j l : ν}, j ≠ l → b i j ⬝ᵥ b i l = 1)
    (hcol : ∀ {i k : μ}, i ≠ k → ∀ j, b i j ⬝ᵥ b k j = 1)
    (hzero : ∀ {i k : μ} {j l : ν}, i ≠ k → j ≠ l → b i j ⬝ᵥ b k l = 0) :
    IsGramArray b := by
  intro i j k l
  by_cases hik : i = k <;> by_cases hjl : j = l
  · subst hik; subst hjl; simpa using hself i j
  · subst hik; simpa [hjl] using hrow i hjl
  · subst hjl; simpa [hik] using hcol hik j
  · simpa [hik, hjl] using hzero hik hjl

theorem IsGramArray.mul_nonneg [Nontrivial μ] [Nontrivial ν] {b : μ → ν → ι → ℤ}
    (hb : IsGramArray b) {i k : μ} {j l : ν} (hne : (i, j) ≠ (k, l)) (hline : i = k ∨ j = l)
    (a : ι) : 0 ≤ b i j a * b k l a := by
  rcases hline with rfl | rfl
  ·
    have hjl : j ≠ l := fun h => hne (by rw [h])
    obtain ⟨i', hi'⟩ := exists_ne i
    exact mul_nonneg_of_dotProduct_eq_three_of_witness (hb.dotProduct_self i j)
      (hb.dotProduct_self i l) (hb.dotProduct_row i hjl)
      (hb.dotProduct_col hi' j) (hb.dotProduct_eq_zero hi' hjl) a
  ·
    have hik : i ≠ k := fun h => hne (by rw [h])
    obtain ⟨j', hj'⟩ := exists_ne j
    exact mul_nonneg_of_dotProduct_eq_three_of_witness (hb.dotProduct_self i j)
      (hb.dotProduct_self k j) (hb.dotProduct_col hik j)
      (hb.dotProduct_row i hj') (hb.dotProduct_eq_zero hik hj') a

theorem mul_nonneg_of_isGramArray_fin {d m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) {i k : Fin m} {j l : Fin n}
    (hne : (i, j) ≠ (k, l)) (hline : i = k ∨ j = l) (a : Fin d) :
    0 ≤ b i j a * b k l a :=
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  hb.mul_nonneg hne hline a

end CFSG.FeitThompson
