module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.LyPerm

open Equiv Equiv.Perm

@[expose] def PairData (σ : Perm (Fin 11)) : Prop :=
  ∃ (p q r s p' q' r' s' : Fin 11) (g : Perm (Fin 11)),
    [p, q, r, s, p', q', r', s'].Nodup ∧
    (swap p q * swap r s) * σ = σ * (swap p q * swap r s) ∧
    (swap p' q' * swap r' s') * σ = σ * (swap p' q' * swap r' s') ∧
    g ∈ alternatingGroup (Fin 11) ∧ g * σ = σ * g ∧
    swap p' q' * swap r' s' = g * (swap p q * swap r s) * g⁻¹

theorem PairData.conj {σ : Perm (Fin 11)} (h : PairData σ) (c : Perm (Fin 11)) :
    PairData (c * σ * c⁻¹) := by
  obtain ⟨p, q, r, s, p', q', r', s', g, hnd, h1, h2, hg, hgσ, hconj⟩ := h
  have hsw : ∀ a b : Fin 11, swap (c a) (c b) = c * swap a b * c⁻¹ := swap_apply_apply c
  refine ⟨c p, c q, c r, c s, c p', c q', c r', c s', c * g * c⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : [c p, c q, c r, c s, c p', c q', c r', c s'] =
        [p, q, r, s, p', q', r', s'].map c := rfl
    rw [this]
    exact hnd.map c.injective
  · rw [hsw, hsw]
    calc c * swap p q * c⁻¹ * (c * swap r s * c⁻¹) * (c * σ * c⁻¹) =
          c * ((swap p q * swap r s) * σ) * c⁻¹ := by group
      _ = c * (σ * (swap p q * swap r s)) * c⁻¹ := by rw [h1]
      _ = c * σ * c⁻¹ * (c * swap p q * c⁻¹ * (c * swap r s * c⁻¹)) := by group
  · rw [hsw, hsw]
    calc c * swap p' q' * c⁻¹ * (c * swap r' s' * c⁻¹) * (c * σ * c⁻¹) =
          c * ((swap p' q' * swap r' s') * σ) * c⁻¹ := by group
      _ = c * (σ * (swap p' q' * swap r' s')) * c⁻¹ := by rw [h2]
      _ = c * σ * c⁻¹ * (c * swap p' q' * c⁻¹ * (c * swap r' s' * c⁻¹)) := by group
  · rw [Perm.mem_alternatingGroup] at hg ⊢
    rw [map_mul, map_mul, map_inv, hg]
    simp
  · calc c * g * c⁻¹ * (c * σ * c⁻¹) = c * (g * σ) * c⁻¹ := by group
      _ = c * (σ * g) * c⁻¹ := by rw [hgσ]
      _ = c * σ * c⁻¹ * (c * g * c⁻¹) := by group
  · rw [hsw, hsw, hsw, hsw]
    calc c * swap p' q' * c⁻¹ * (c * swap r' s' * c⁻¹) =
          c * (swap p' q' * swap r' s') * c⁻¹ := by group
      _ = c * (g * (swap p q * swap r s) * g⁻¹) * c⁻¹ := by rw [hconj]
      _ = c * g * c⁻¹ * (c * swap p q * c⁻¹ * (c * swap r s * c⁻¹)) * (c * g * c⁻¹)⁻¹ := by group

@[expose] def std : ℕ → Perm (Fin 11)
  | 0 => 1
  | 1 => swap 0 1
  | 2 => swap 0 1 * swap 2 3
  | 3 => swap 0 1 * swap 2 3 * swap 4 5
  | 4 => swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7
  | _ => swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9

theorem cycleType_swap_eq {a b : Fin 11} (h : a ≠ b) : (swap a b).cycleType = {2} := by
  rw [(isCycle_swap h).cycleType, card_support_swap h]

theorem disjoint_of_forall (a b : Perm (Fin 11)) (h : ∀ x : Fin 11, a x = x ∨ b x = x) :
    Disjoint a b := h

theorem cycleType_std {k : ℕ} (hk : k ≤ 5) : (std k).cycleType = Multiset.replicate k 2 := by
  have h01 : (swap (0 : Fin 11) 1).cycleType = {2} := cycleType_swap_eq (by decide)
  have h23 : (swap (2 : Fin 11) 3).cycleType = {2} := cycleType_swap_eq (by decide)
  have h45 : (swap (4 : Fin 11) 5).cycleType = {2} := cycleType_swap_eq (by decide)
  have h67 : (swap (6 : Fin 11) 7).cycleType = {2} := cycleType_swap_eq (by decide)
  have h89 : (swap (8 : Fin 11) 9).cycleType = {2} := cycleType_swap_eq (by decide)
  have d1 : Disjoint (swap (0 : Fin 11) 1) (swap 2 3) :=
    disjoint_of_forall _ _ (by decide +kernel)
  have d2 : Disjoint (swap (0 : Fin 11) 1 * swap 2 3) (swap 4 5) :=
    disjoint_of_forall _ _ (by decide +kernel)
  have d3 : Disjoint (swap (0 : Fin 11) 1 * swap 2 3 * swap 4 5) (swap 6 7) :=
    disjoint_of_forall _ _ (by decide +kernel)
  have d4 : Disjoint (swap (0 : Fin 11) 1 * swap 2 3 * swap 4 5 * swap 6 7) (swap 8 9) :=
    disjoint_of_forall _ _ (by decide +kernel)
  interval_cases k
  · simp [std]
  · simpa [std] using h01
  · simp only [std, d1.cycleType_mul, h01, h23]
    rfl
  · simp only [std, d2.cycleType_mul, d1.cycleType_mul, h01, h23, h45]
    rfl
  · simp only [std, d3.cycleType_mul, d2.cycleType_mul, d1.cycleType_mul, h01, h23, h45, h67]
    rfl
  · simp only [std, d4.cycleType_mul, d3.cycleType_mul, d2.cycleType_mul, d1.cycleType_mul, h01, h23,
      h45, h67, h89]
    rfl

theorem mem_alt_of_sign {g : Perm (Fin 11)} (h : Perm.sign g = 1) : g ∈ alternatingGroup (Fin 11) :=
  Perm.mem_alternatingGroup.2 h

theorem pairData_std {k : ℕ} (hk : k ≤ 5) : PairData (std k) := by
  interval_cases k
  · exact ⟨0, 1, 2, 3, 4, 5, 6, 7, swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7, by decide +kernel,
      by decide +kernel, by decide +kernel, mem_alt_of_sign (by decide +kernel), by decide +kernel,
      by decide +kernel⟩
  · exact ⟨2, 3, 4, 5, 6, 7, 8, 9, swap 2 6 * swap 3 7 * swap 4 8 * swap 5 9, by decide +kernel,
      by decide +kernel, by decide +kernel, mem_alt_of_sign (by decide +kernel), by decide +kernel,
      by decide +kernel⟩
  · exact ⟨0, 1, 4, 5, 2, 3, 6, 7, swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7, by decide +kernel,
      by decide +kernel, by decide +kernel, mem_alt_of_sign (by decide +kernel), by decide +kernel,
      by decide +kernel⟩
  · exact ⟨0, 1, 6, 7, 2, 3, 8, 9, swap 0 2 * swap 1 3 * swap 6 8 * swap 7 9, by decide +kernel,
      by decide +kernel, by decide +kernel, mem_alt_of_sign (by decide +kernel), by decide +kernel,
      by decide +kernel⟩
  · exact ⟨0, 1, 2, 3, 4, 5, 6, 7, swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7, by decide +kernel,
      by decide +kernel, by decide +kernel, mem_alt_of_sign (by decide +kernel), by decide +kernel,
      by decide +kernel⟩
  · exact ⟨0, 1, 2, 3, 4, 5, 6, 7, swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7, by decide +kernel,
      by decide +kernel, by decide +kernel, mem_alt_of_sign (by decide +kernel), by decide +kernel,
      by decide +kernel⟩

theorem invol_cycleType (σ : Perm (Fin 11)) (hσ : σ * σ = 1) :
    ∃ k : ℕ, k ≤ 5 ∧ σ.cycleType = Multiset.replicate k 2 := by
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hσ)
  have hall : ∀ n ∈ σ.cycleType, n = 2 := fun n hn =>
    ((Nat.dvd_prime Nat.prime_two).1 ((dvd_of_mem_cycleType hn).trans hord)).resolve_left
      (by have := two_le_of_mem_cycleType hn; omega)
  refine ⟨σ.cycleType.card, ?_, Multiset.eq_replicate_of_mem hall⟩
  have h1 := sum_cycleType σ
  have h2 : σ.cycleType.sum = 2 * σ.cycleType.card := by
    conv_lhs => rw [Multiset.eq_replicate_of_mem hall]
    simp [mul_comm]
  have h3 : σ.support.card ≤ 11 := by
    have := Finset.card_le_univ σ.support
    simpa using this
  omega

theorem exists_pair_data (σ : Perm (Fin 11)) (hσ : σ * σ = 1) : PairData σ := by
  obtain ⟨k, hk, hct⟩ := invol_cycleType σ hσ
  have hconj : IsConj (std k) σ := isConj_iff_cycleType_eq.2 (by rw [hct, cycleType_std hk])
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  rw [← hc]
  exact (pairData_std hk).conj c

end CFSG.GH74.Uniqueness.SU.K.R4.LyPerm
