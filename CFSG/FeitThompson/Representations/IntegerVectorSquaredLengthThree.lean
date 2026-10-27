module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.Int.Star

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset Matrix

variable {ι : Type*}

def IsSignedCoordVec [DecidableEq ι] (v : ι → ℤ) : Prop :=
  ∃ i : ι, v = Pi.single i 1 ∨ v = Pi.single i (-1)

section DecEq

variable [DecidableEq ι] {v : ι → ℤ}

theorem isSignedCoordVec_single_one (i : ι) : IsSignedCoordVec (Pi.single i (1 : ℤ)) :=
  ⟨i, Or.inl rfl⟩

theorem isSignedCoordVec_single_neg_one (i : ι) : IsSignedCoordVec (Pi.single i (-1 : ℤ)) :=
  ⟨i, Or.inr rfl⟩

theorem isSignedCoordVec_single {i : ι} {a : ℤ} (ha : a = 1 ∨ a = -1) :
    IsSignedCoordVec (Pi.single i a) := by
  rcases ha with rfl | rfl
  · exact isSignedCoordVec_single_one i
  · exact isSignedCoordVec_single_neg_one i

theorem support_single_of_ne_zero (i : ι) {a : ℤ} (ha : a ≠ 0) :
    Function.support (Pi.single i a) = {i} := by
  ext m
  simp [ha, eq_comm]

theorem IsSignedCoordVec.exists_support_eq (hv : IsSignedCoordVec v) :
    ∃ i : ι, Function.support v = {i} ∧ (v i = 1 ∨ v i = -1) := by
  obtain ⟨i, rfl | rfl⟩ := hv
  · exact ⟨i, support_single_of_ne_zero i one_ne_zero, Or.inl (by simp)⟩
  · exact ⟨i, support_single_of_ne_zero i (by norm_num), Or.inr (by simp)⟩

theorem isSignedCoordVec_of_support_eq {i : ι} (hsupp : Function.support v = {i})
    (hv : v i = 1 ∨ v i = -1) : IsSignedCoordVec v := by
  have hzero : ∀ m, m ≠ i → v m = 0 := by
    intro m hm
    by_contra h
    exact hm (by simpa [hsupp] using Function.mem_support.mpr h)
  have hsingle : v = Pi.single i (v i) := by
    funext m
    by_cases hm : m = i
    · subst hm; simp
    · simp [hzero m hm, hm]
  rw [hsingle]
  exact isSignedCoordVec_single hv

theorem sum_single_eq_self {u : ι → ℤ} {s : Finset ι} (hs : ∀ i, u i ≠ 0 → i ∈ s) :
    ∑ i ∈ s, Pi.single i (u i) = u := by
  funext m
  simp only [Finset.sum_apply, Finset.sum_pi_single]
  by_cases hm : m ∈ s
  · simp [hm]
  · simp only [hm, if_false]
    exact (not_not.mp fun h => hm (hs m h)).symm

end DecEq

section Fintype

variable [Fintype ι] {u : ι → ℤ}

theorem sq_le_dotProduct_self (u : ι → ℤ) (i : ι) : u i ^ 2 ≤ u ⬝ᵥ u := by
  rw [dotProduct, sq]
  exact Finset.single_le_sum (f := fun j => u j * u j)
    (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)

theorem eq_one_or_neg_one_of_dotProduct_self_eq_three (hu : u ⬝ᵥ u = 3) {i : ι}
    (hi : u i ≠ 0) : u i = 1 ∨ u i = -1 :=
  sq_eq_one_iff.mp (Int.sq_eq_one_of_sq_le_three (hu ▸ sq_le_dotProduct_self u i) hi)

theorem card_support_eq_three_of_dotProduct_self_eq_three (hu : u ⬝ᵥ u = 3) :
    #{i | u i ≠ 0} = 3 := by
  have key : ∀ i ∈ ({i | u i ≠ 0} : Finset ι), u i * u i = 1 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases eq_one_or_neg_one_of_dotProduct_self_eq_three hu hi with h | h <;> simp [h]
  have h3 := hu
  rw [dotProduct, ← Finset.sum_subset (Finset.subset_univ ({i | u i ≠ 0} : Finset ι))
    (fun i _ hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simp [hi]), Finset.sum_congr rfl key, Finset.sum_const] at h3
  simp only [nsmul_eq_mul, mul_one] at h3
  exact_mod_cast h3

variable [DecidableEq ι]

theorem IsSignedCoordVec.dotProduct_self {v : ι → ℤ} (hv : IsSignedCoordVec v) : v ⬝ᵥ v = 1 := by
  obtain ⟨i, rfl | rfl⟩ := hv <;> simp [dotProduct, Pi.single_apply]

theorem exists_eq_sum_three_isSignedCoordVec (hu : u ⬝ᵥ u = 3) :
    ∃ v₁ v₂ v₃ : ι → ℤ, IsSignedCoordVec v₁ ∧ IsSignedCoordVec v₂ ∧ IsSignedCoordVec v₃ ∧
      Function.support v₁ ≠ Function.support v₂ ∧
      Function.support v₁ ≠ Function.support v₃ ∧
      Function.support v₂ ≠ Function.support v₃ ∧
      u = v₁ + v₂ + v₃ := by
  obtain ⟨i, j, k, hij, hik, hjk, hs⟩ :=
    Finset.card_eq_three.mp (card_support_eq_three_of_dotProduct_self_eq_three hu)
  have hmem : ∀ m : ι, u m ≠ 0 → m ∈ ({i, j, k} : Finset ι) := by
    intro m hm; rw [← hs]; simpa using hm
  have hne : ∀ m ∈ ({i, j, k} : Finset ι), u m ≠ 0 := by
    intro m hm
    rw [← hs] at hm
    simpa using hm
  have hi := hne i (by simp)
  have hj := hne j (by simp)
  have hk := hne k (by simp)
  refine ⟨Pi.single i (u i), Pi.single j (u j), Pi.single k (u k),
    isSignedCoordVec_single (eq_one_or_neg_one_of_dotProduct_self_eq_three hu hi),
    isSignedCoordVec_single (eq_one_or_neg_one_of_dotProduct_self_eq_three hu hj),
    isSignedCoordVec_single (eq_one_or_neg_one_of_dotProduct_self_eq_three hu hk),
    ?_, ?_, ?_, ?_⟩
  · rw [support_single_of_ne_zero i hi, support_single_of_ne_zero j hj]
    simpa using hij
  · rw [support_single_of_ne_zero i hi, support_single_of_ne_zero k hk]
    simpa using hik
  · rw [support_single_of_ne_zero j hj, support_single_of_ne_zero k hk]
    simpa using hjk
  · have h := sum_single_eq_self (u := u) hmem
    rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
      Finset.sum_singleton] at h
    rw [add_assoc]
    exact h.symm

end Fintype

theorem exists_three_indices_of_dotProduct_self_eq_three {d : ℕ} {u : Fin d → ℤ}
    (hu : u ⬝ᵥ u = 3) :
    ∃ i j k : Fin d, ∃ a b c : ℤ, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ (c = 1 ∨ c = -1) ∧
      u = Pi.single i a + Pi.single j b + Pi.single k c := by
  obtain ⟨i, j, k, hij, hik, hjk, hs⟩ :=
    Finset.card_eq_three.mp (card_support_eq_three_of_dotProduct_self_eq_three hu)
  have hmem : ∀ m : Fin d, u m ≠ 0 → m ∈ ({i, j, k} : Finset (Fin d)) := by
    intro m hm; rw [← hs]; simpa using hm
  have hne : ∀ m ∈ ({i, j, k} : Finset (Fin d)), u m ≠ 0 := by
    intro m hm
    rw [← hs] at hm
    simpa using hm
  refine ⟨i, j, k, u i, u j, u k, hij, hik, hjk,
    eq_one_or_neg_one_of_dotProduct_self_eq_three hu (hne i (by simp)),
    eq_one_or_neg_one_of_dotProduct_self_eq_three hu (hne j (by simp)),
    eq_one_or_neg_one_of_dotProduct_self_eq_three hu (hne k (by simp)), ?_⟩
  have h := sum_single_eq_self (u := u) hmem
  rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
    Finset.sum_singleton] at h
  rw [add_assoc]
  exact h.symm

end CFSG.FeitThompson
