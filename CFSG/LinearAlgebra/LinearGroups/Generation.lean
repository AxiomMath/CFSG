module

public import CFSG.LinearAlgebra.LinearGroups.Elementary

public section

namespace CFSG.LinearGroups

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem list_prod_diagonal {ι : Type*} (L : List ι) (f : ι → Fin n → K) :
    (L.map fun i => diagonal (f i)).prod = diagonal (fun k => (L.map fun i => f i k).prod) := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, diagonal_mul_diagonal]; simp

theorem special_linear_diagonal_generation (hn : 2 ≤ n) (d : Fin n → Kˣ)
    (hd : ∏ i, (d i : K) = 1) :
    diagonal (fun k => (d k : K)) =
        (((List.finRange n).filter (fun i => i ≠ ⟨n - 1, by omega⟩)).map fun i =>
          diagonal (fun k => if k = i then (d i : K) else
            if k = ⟨n - 1, by omega⟩ then (d i : K)⁻¹ else 1)).prod ∧
      ∃ h : (diagonal (fun k => (d k : K))).det = 1,
        (⟨_, h⟩ : SpecialLinearGroup (Fin n) K) ∈ Subgroup.closure (elementarySet n K) := by
  classical
  set l : Fin n := ⟨n - 1, by omega⟩ with hl
  have hdet : (diagonal (fun k => (d k : K))).det = 1 := by rw [det_diagonal]; exact hd
  refine ⟨?_, hdet, ?_⟩
  · rw [list_prod_diagonal]
    congr 1
    funext k
    rw [← List.prod_toFinset _ ((List.nodup_finRange n).filter _), List.toFinset_filter,
      List.toFinset_finRange]
    simp only [decide_eq_true_eq, Finset.filter_ne']
    by_cases hk : k = l
    · subst hk
      have hprod := Finset.mul_prod_erase Finset.univ (fun i => (d i : K)) (Finset.mem_univ l)
      rw [hd] at hprod
      have hrest : ∏ x ∈ Finset.univ.erase l, (d x : K) = (d l : K)⁻¹ :=
        eq_inv_of_mul_eq_one_right hprod
      rw [Finset.prod_congr rfl fun i hi => by
        rw [ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hi)), ite_eq_left rfl],
        Finset.prod_inv_distrib, hrest, inv_inv]
    · rw [Finset.prod_congr rfl fun i _ => by rw [ite_eq_right hk] , Finset.prod_ite_eq,
        ite_eq_left (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)]
  · have key : (⟨diagonal (fun k => (d k : K)), hdet⟩ : SpecialLinearGroup (Fin n) K) = _ :=
      SpecialLinearGroup.diag_eq_diag2n_prod l _ hdet
    rw [key]
    refine Subgroup.noncommProd_mem (G := SpecialLinearGroup (Fin n) K) _ _ fun i hi => ?_
    have hi' : i ≠ l := (Finset.mem_filter.mp hi).2
    rw [dite_eq_left hi']
    exact (elementary_diagonal_factorization hi' _).2.2.2.2

theorem special_linear_elementary_generation :
    Subgroup.closure (elementarySet n K) = ⊤ := by
  rw [← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin n) (K := K)]
  congr 1
  ext A
  constructor
  · rintro ⟨i, j, hij, c, rfl⟩
    exact ⟨⟨i, j, hij, c⟩, rfl⟩
  · rintro ⟨⟨i, j, hij, c⟩, rfl⟩
    exact ⟨i, j, hij, c, rfl⟩

theorem field_scalar_with_nontrivial_square (hK : ∃ s : Finset K, s.card = 4) :
    ∃ l : Kˣ, l ^ 2 ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ := hK
  by_contra h
  push Not at h
  have hsub : s ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have h2 := congrArg Units.val (h (Units.mk0 a ha))
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h2
      rcases sq_eq_one_iff.mp h2 with rfl | rfl <;> simp
  have h3 : ({0, 1, -1} : Finset K).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (by simp)))
  have := Finset.card_le_card hsub
  omega

theorem exists_finset_card_eq_four {α : Type*} (hα : 4 ≤ Nat.card α) :
    ∃ s : Finset α, s.card = 4 := by
  have : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite α
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset α)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hα)
  exact ⟨s, hs⟩

end CFSG.LinearGroups
