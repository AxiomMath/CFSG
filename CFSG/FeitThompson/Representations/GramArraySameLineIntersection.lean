module

public import CFSG.FeitThompson.Representations.GramArrayLineNoOppositeSigns
import CFSG.FeitThompson.Representations.IntegerVectorSquaredLengthThree
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset Matrix

section Aux

variable {ι : Type*} [Fintype ι]

theorem exists_support_inter_eq_singleton_of_dotProduct {u v : ι → ℤ}
    (hu : u ⬝ᵥ u = 3) (hv : v ⬝ᵥ v = 3) (huv : u ⬝ᵥ v = 1)
    (hsign : ∀ a, 0 ≤ u a * v a) :
    ∃ a, Function.support u ∩ Function.support v = {a} ∧ u a = v a ∧
      (u a = 1 ∨ u a = -1) := by
  classical
  have hprod : ∀ a, u a * v a = 0 ∨ u a * v a = 1 := by
    intro a
    by_cases hua : u a = 0
    · left; simp [hua]
    by_cases hva : v a = 0
    · left; simp [hva]
    have h1 := eq_one_or_neg_one_of_dotProduct_self_eq_three hu hua
    have h2 := eq_one_or_neg_one_of_dotProduct_self_eq_three hv hva
    have h3 := hsign a
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at h3 ⊢ <;> omega
  set s : Finset ι := {a | u a * v a ≠ 0} with hs
  have hmem : ∀ m, m ∈ s ↔ (u m ≠ 0 ∧ v m ≠ 0) := by
    intro m; simp [hs]
  have hsum : ∑ a ∈ s, u a * v a = ∑ a, u a * v a :=
    Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => by
      have h := (hmem a).not.mp ha
      rw [not_and_or, not_not, not_not] at h
      rcases h with h | h <;> simp [h])
  have hcard : (#s : ℤ) = 1 := by
    have hval : ∑ a ∈ s, u a * v a = #s := by
      rw [Finset.sum_congr rfl (fun a ha => ?_), Finset.sum_const, nsmul_eq_mul, mul_one]
      exact (hprod a).resolve_left (mul_ne_zero ((hmem a).mp ha).1 ((hmem a).mp ha).2)
    rw [← hval, hsum, ← dotProduct]
    exact huv
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by exact_mod_cast hcard)
  have has : a ∈ s := by simp [ha]
  obtain ⟨hua, hva⟩ := (hmem a).mp has
  have h1 : u a * v a = 1 := (hprod a).resolve_left (mul_ne_zero hua hva)
  refine ⟨a, ?_, ?_, eq_one_or_neg_one_of_dotProduct_self_eq_three hu hua⟩
  · ext m
    simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_singleton_iff]
    rw [← hmem m, ha]
    simp
  · rcases eq_one_or_neg_one_of_dotProduct_self_eq_three hu hua with h | h <;>
      rcases eq_one_or_neg_one_of_dotProduct_self_eq_three hv hva with h' | h' <;>
      rw [h, h'] at h1 ⊢ <;> omega

end Aux

variable {μ ν ι : Type*} [DecidableEq μ] [DecidableEq ν] [Fintype ι]

theorem IsGramArray.exists_support_inter_eq_singleton [Nontrivial μ] [Nontrivial ν]
    {b : μ → ν → ι → ℤ} (hb : IsGramArray b) {i k : μ} {j l : ν} (hne : (i, j) ≠ (k, l))
    (hline : i = k ∨ j = l) :
    ∃ a, Function.support (b i j) ∩ Function.support (b k l) = {a} ∧
      b i j a = b k l a ∧ (b i j a = 1 ∨ b i j a = -1) := by
  have hdot : b i j ⬝ᵥ b k l = 1 := by
    rcases hline with rfl | rfl
    · exact hb.dotProduct_row i fun h => hne (by rw [h])
    · exact hb.dotProduct_col (fun h => hne (by rw [h])) j
  exact exists_support_inter_eq_singleton_of_dotProduct (hb.dotProduct_self i j)
    (hb.dotProduct_self k l) hdot (hb.mul_nonneg hne hline)

theorem IsGramArray.existsUnique_mem_support [Nontrivial μ] [Nontrivial ν] {b : μ → ν → ι → ℤ}
    (hb : IsGramArray b) {i k : μ} {j l : ν} (hne : (i, j) ≠ (k, l)) (hline : i = k ∨ j = l) :
    ∃! a, b i j a ≠ 0 ∧ b k l a ≠ 0 := by
  obtain ⟨a, hsupp, -⟩ := hb.exists_support_inter_eq_singleton hne hline
  have key : ∀ m, (b i j m ≠ 0 ∧ b k l m ≠ 0) ↔ m = a := by
    intro m
    have := Set.ext_iff.mp hsupp m
    simpa [Function.mem_support] using this
  exact ⟨a, (key a).mpr rfl, fun m hm => (key m).mp hm⟩

theorem exists_support_inter_eq_singleton_of_isGramArray_fin {d m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) {i k : Fin m} {j l : Fin n}
    (hne : (i, j) ≠ (k, l)) (hline : i = k ∨ j = l) :
    ∃ a : Fin d, Function.support (b i j) ∩ Function.support (b k l) = {a} ∧
      b i j a = b k l a ∧ (b i j a = 1 ∨ b i j a = -1) :=
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  hb.exists_support_inter_eq_singleton hne hline

end CFSG.FeitThompson
