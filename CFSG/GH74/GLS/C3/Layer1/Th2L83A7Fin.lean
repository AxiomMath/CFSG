module

public import CFSG.GH74.GLS.IVK.Proofs2.A7Crit
public import CFSG.GH74.GLS.C3.Layer1.Th2A7

public section

namespace CFSG.GH74.GLS.Th2.L83

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.IVK.A7 CFSG.GH74.GLS.IVK.Proofs2.A7Fin

@[expose] def c1 : Perm (Fin 7) := swap 4 5 * swap 4 6

@[expose] def c2 : Perm (Fin 7) := swap 1 3 * swap 1 6

@[expose] def c3 : Perm (Fin 7) := swap 0 2 * swap 0 6

theorem c1_three : c1.IsThreeCycle :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem alt_le_of_c123 (H : Subgroup (Perm (Fin 7))) (h1 : c1 ∈ H) (h2 : c2 ∈ H) (h3 : c3 ∈ H) :
    alternatingGroup (Fin 7) ≤ H := by
  refine jordan7 H ?_ c1_three h1
  intro j
  have e1 : c1 ^ 2 ∈ H := H.pow_mem h1 2
  have e2 : c2 ^ 2 ∈ H := H.pow_mem h2 2
  have e3 : c3 ^ 2 ∈ H := H.pow_mem h3 2
  fin_cases j
  · exact ⟨c3 ^ 2, e3, by decide⟩
  · exact ⟨c2 ^ 2, e2, by decide⟩
  · exact ⟨c3, h3, by decide⟩
  · exact ⟨c2, h2, by decide⟩
  · exact ⟨c1 ^ 2, e1, by decide⟩
  · exact ⟨c1, h1, by decide⟩
  · exact ⟨1, H.one_mem, by decide⟩

def ZVals (σ : Perm (Fin 7)) : Prop :=
  σ 6 = 6 ∧ (σ 0 = 0 ∧ σ 2 = 2 ∨ σ 0 = 2 ∧ σ 2 = 0) ∧ (σ 1 = 1 ∧ σ 3 = 3 ∨ σ 1 = 3 ∧ σ 3 = 1) ∧
    (σ 4 = 4 ∧ σ 5 = 5 ∨ σ 4 = 5 ∧ σ 5 = 4)

theorem fixa_aux : ∀ j : Fin 7, (swap 0 2 * swap 1 3 : Perm (Fin 7)) j = j → j = 4 ∨ j = 5 ∨ j = 6 := by
  decide

theorem fixb_aux : ∀ j : Fin 7, (swap 0 2 * swap 4 5 : Perm (Fin 7)) j = j → j = 1 ∨ j = 3 ∨ j = 6 := by
  decide

theorem fixab_aux : ∀ j : Fin 7, (swap 0 2 * swap 1 3 : Perm (Fin 7)) j = j →
    (swap 0 2 * swap 4 5 : Perm (Fin 7)) j = j → j = 6 := by
  decide

theorem eqab_aux : ∀ j : Fin 7, (swap 0 2 * swap 1 3 : Perm (Fin 7)) j = (swap 0 2 * swap 4 5 : Perm (Fin 7)) j →
    j = 0 ∨ j = 2 ∨ j = 6 := by
  decide

theorem centralizer_pair_zvals (σ : Perm (Fin 7))
    (ha : σ * (swap 0 2 * swap 1 3) = (swap 0 2 * swap 1 3) * σ)
    (hb : σ * (swap 0 2 * swap 4 5) = (swap 0 2 * swap 4 5) * σ) : ZVals σ := by
  have ea : ∀ i, σ ((swap 0 2 * swap 1 3 : Perm (Fin 7)) i) =
      (swap 0 2 * swap 1 3 : Perm (Fin 7)) (σ i) := fun i => by
    have := congrArg (fun p : Perm (Fin 7) => p i) ha
    simpa only [Perm.mul_apply] using this
  have eb : ∀ i, σ ((swap 0 2 * swap 4 5 : Perm (Fin 7)) i) =
      (swap 0 2 * swap 4 5 : Perm (Fin 7)) (σ i) := fun i => by
    have := congrArg (fun p : Perm (Fin 7) => p i) hb
    simpa only [Perm.mul_apply] using this
  have a0 : (swap 0 2 * swap 1 3 : Perm (Fin 7)) 0 = 2 := by decide
  have a1 : (swap 0 2 * swap 1 3 : Perm (Fin 7)) 1 = 3 := by decide
  have a4 : (swap 0 2 * swap 1 3 : Perm (Fin 7)) 4 = 4 := by decide
  have a6 : (swap 0 2 * swap 1 3 : Perm (Fin 7)) 6 = 6 := by decide
  have b0 : (swap 0 2 * swap 4 5 : Perm (Fin 7)) 0 = 2 := by decide
  have b1 : (swap 0 2 * swap 4 5 : Perm (Fin 7)) 1 = 1 := by decide
  have b4 : (swap 0 2 * swap 4 5 : Perm (Fin 7)) 4 = 5 := by decide
  have b6 : (swap 0 2 * swap 4 5 : Perm (Fin 7)) 6 = 6 := by decide
  have h6 : σ 6 = 6 := by
    have h1 := ea 6
    have h2 := eb 6
    rw [a6] at h1
    rw [b6] at h2
    exact fixab_aux (σ 6) h1.symm h2.symm
  have hne6 : ∀ i, i ≠ 6 → σ i ≠ 6 := fun i hi h => hi (σ.injective (h.trans h6.symm))
  have h0 : σ 0 = 0 ∨ σ 0 = 2 := by
    have h1 := ea 0
    have h2 := eb 0
    rw [a0] at h1
    rw [b0] at h2
    rcases eqab_aux (σ 0) (h1.symm.trans h2) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hne6 0 (by decide))
  have h1 : σ 1 = 1 ∨ σ 1 = 3 := by
    have h2 := eb 1
    rw [b1] at h2
    rcases fixb_aux (σ 1) h2.symm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hne6 1 (by decide))
  have h4 : σ 4 = 4 ∨ σ 4 = 5 := by
    have h2 := ea 4
    rw [a4] at h2
    rcases fixa_aux (σ 4) h2.symm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hne6 4 (by decide))
  refine ⟨h6, ?_, ?_, ?_⟩
  · have s := ea 0
    have s2 := ea 2
    rw [a0] at s
    have a2 : (swap 0 2 * swap 1 3 : Perm (Fin 7)) 2 = 0 := by decide
    rcases h0 with h | h
    · left
      refine ⟨h, ?_⟩
      rw [s, h]
      exact a0
    · right
      refine ⟨h, ?_⟩
      rw [s, h]
      exact a2
  · have s := ea 1
    rw [a1] at s
    have a3 : (swap 0 2 * swap 1 3 : Perm (Fin 7)) 3 = 1 := by decide
    rcases h1 with h | h
    · left
      refine ⟨h, ?_⟩
      rw [s, h]
      exact a1
    · right
      refine ⟨h, ?_⟩
      rw [s, h]
      exact a3
  · have s := eb 4
    rw [b4] at s
    have b5 : (swap 0 2 * swap 4 5 : Perm (Fin 7)) 5 = 4 := by decide
    rcases h4 with h | h
    · left
      refine ⟨h, ?_⟩
      rw [s, h]
      exact b4
    · right
      refine ⟨h, ?_⟩
      rw [s, h]
      exact b5

theorem centralizer_Wsub_zvals (σ : Perm (Fin 7)) (h : ∀ w ∈ Wsub, σ * w = w * σ) : ZVals σ := by
  have h1 : (swap 0 2 * swap 1 3 : Perm (Fin 7)) ∈ Wsub := by
    rw [CFSG.GH74.GLS.Th2.A7Aux.mem_Wsub_iff]
    simp only [CFSG.GH74.GLS.Th2.A7Aux.Wlist, List.mem_cons, List.not_mem_nil, or_false]
    right; left; decide
  have h2 : (swap 0 2 * swap 4 5 : Perm (Fin 7)) ∈ Wsub := by
    rw [CFSG.GH74.GLS.Th2.A7Aux.mem_Wsub_iff]
    simp only [CFSG.GH74.GLS.Th2.A7Aux.Wlist, List.mem_cons, List.not_mem_nil, or_false]
    right; right; left; decide
  exact centralizer_pair_zvals σ (h _ h1) (h _ h2)

theorem conj_three_cycle (σ : Perm (Fin 7)) (p q r : Fin 7) :
    σ * (swap p q * swap p r) * σ⁻¹ = swap (σ p) (σ q) * swap (σ p) (σ r) := by
  rw [swap_apply_apply σ p q, swap_apply_apply σ p r]
  group

theorem conj_c1 (σ : Perm (Fin 7)) (h : ZVals σ) : σ * c1 * σ⁻¹ = c1 ∨ σ * c1 * σ⁻¹ = c1⁻¹ := by
  obtain ⟨h6, -, -, h45⟩ := h
  have e : σ * c1 * σ⁻¹ = swap (σ 4) (σ 5) * swap (σ 4) (σ 6) := conj_three_cycle σ 4 5 6
  rcases h45 with ⟨h4, h5⟩ | ⟨h4, h5⟩
  · left; rw [e, h4, h5, h6]; rfl
  · right; rw [e, h4, h5, h6]; unfold c1; decide

theorem conj_c2 (σ : Perm (Fin 7)) (h : ZVals σ) : σ * c2 * σ⁻¹ = c2 ∨ σ * c2 * σ⁻¹ = c2⁻¹ := by
  obtain ⟨h6, -, h13, -⟩ := h
  have e : σ * c2 * σ⁻¹ = swap (σ 1) (σ 3) * swap (σ 1) (σ 6) := conj_three_cycle σ 1 3 6
  rcases h13 with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · left; rw [e, h1, h3, h6]; rfl
  · right; rw [e, h1, h3, h6]; unfold c2; decide

theorem conj_c3 (σ : Perm (Fin 7)) (h : ZVals σ) : σ * c3 * σ⁻¹ = c3 ∨ σ * c3 * σ⁻¹ = c3⁻¹ := by
  obtain ⟨h6, h02, -, -⟩ := h
  have e : σ * c3 * σ⁻¹ = swap (σ 0) (σ 2) * swap (σ 0) (σ 6) := conj_three_cycle σ 0 2 6
  rcases h02 with ⟨h0, h2⟩ | ⟨h0, h2⟩
  · left; rw [e, h0, h2, h6]; rfl
  · right; rw [e, h0, h2, h6]; unfold c3; decide

theorem commute_mul_of_conj {c σ τ : Perm (Fin 7)}
    (hσ : σ * c * σ⁻¹ = c ∨ σ * c * σ⁻¹ = c⁻¹) (hτ : τ * c * τ⁻¹ = c ∨ τ * c * τ⁻¹ = c⁻¹)
    (h1 : σ * c ≠ c * σ) (h2 : τ * c ≠ c * τ) : (σ * τ) * c = c * (σ * τ) := by
  have e1 : σ * c * σ⁻¹ = c⁻¹ := by
    rcases hσ with h | h
    · exact absurd (mul_inv_eq_iff_eq_mul.1 h) h1
    · exact h
  have e2 : τ * c * τ⁻¹ = c⁻¹ := by
    rcases hτ with h | h
    · exact absurd (mul_inv_eq_iff_eq_mul.1 h) h2
    · exact h
  have : (σ * τ) * c * (σ * τ)⁻¹ = c := by
    calc (σ * τ) * c * (σ * τ)⁻¹ = σ * (τ * c * τ⁻¹) * σ⁻¹ := by group
      _ = σ * c⁻¹ * σ⁻¹ := by rw [e2]
      _ = (σ * c * σ⁻¹)⁻¹ := by group
      _ = c := by rw [e1, inv_inv]
  exact mul_inv_eq_iff_eq_mul.1 this

theorem coset_c1 {σ τ : Perm (Fin 7)} (hσ : ZVals σ) (hτ : ZVals τ) (h1 : σ * c1 ≠ c1 * σ)
    (h2 : τ * c1 ≠ c1 * τ) : (σ * τ) * c1 = c1 * (σ * τ) :=
  commute_mul_of_conj (conj_c1 σ hσ) (conj_c1 τ hτ) h1 h2

theorem coset_c2 {σ τ : Perm (Fin 7)} (hσ : ZVals σ) (hτ : ZVals τ) (h1 : σ * c2 ≠ c2 * σ)
    (h2 : τ * c2 ≠ c2 * τ) : (σ * τ) * c2 = c2 * (σ * τ) :=
  commute_mul_of_conj (conj_c2 σ hσ) (conj_c2 τ hτ) h1 h2

theorem coset_c3 {σ τ : Perm (Fin 7)} (hσ : ZVals σ) (hτ : ZVals τ) (h1 : σ * c3 ≠ c3 * σ)
    (h2 : τ * c3 ≠ c3 * τ) : (σ * τ) * c3 = c3 * (σ * τ) :=
  commute_mul_of_conj (conj_c3 σ hσ) (conj_c3 τ hτ) h1 h2

end CFSG.GH74.GLS.Th2.L83
