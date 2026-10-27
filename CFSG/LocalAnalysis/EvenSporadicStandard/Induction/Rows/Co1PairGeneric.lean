module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.Co1Pair

open Subgroup

variable {G : Type*} [Group G]

theorem exists_mem_of_closure [Finite G] (A : Set G) (H : Subgroup G) (n : ℕ) (t : ℕ → G)
    (h1 : ∃ k < n, t k = 1)
    (hA : ∀ a ∈ A, ∀ k < n, ∃ k' < n, ∃ h ∈ H, a * t k = t k' * h) :
    ∀ g ∈ Subgroup.closure A, ∃ k < n, ∃ h ∈ H, g = t k * h := by
  intro g hg
  have hg' : g ∈ Submonoid.closure A := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  clear hg
  obtain ⟨k₀, hk₀, ht₀⟩ := h1
  induction hg' using Submonoid.closure_induction_left with
  | one => exact ⟨k₀, hk₀, 1, H.one_mem, by rw [ht₀, one_mul]⟩
  | mul_left a ha y _ ih =>
    obtain ⟨k, hk, h, hh, rfl⟩ := ih
    obtain ⟨k', hk', h', hh', e⟩ := hA a ha k hk
    exact ⟨k', hk', h' * h, H.mul_mem hh' hh, by rw [← mul_assoc, e, mul_assoc]⟩

theorem card_closure_le [Finite G] (A : Set G) (H : Subgroup G) (n : ℕ) (t : ℕ → G)
    (h1 : ∃ k < n, t k = 1)
    (hA : ∀ a ∈ A, ∀ k < n, ∃ k' < n, ∃ h ∈ H, a * t k = t k' * h) :
    Nat.card (Subgroup.closure A) ≤ n * Nat.card H := by
  have key := exists_mem_of_closure A H n t h1 hA
  let ψ : Fin n × H → G := fun p => t p.1 * p.2
  have hsub : (Subgroup.closure A : Set G) ⊆ Set.range ψ := by
    intro g hg
    obtain ⟨k, hk, h, hh, rfl⟩ := key g hg
    exact ⟨(⟨k, hk⟩, ⟨h, hh⟩), rfl⟩
  have h2 : Nat.card (Fin n × H) = n * Nat.card H := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  have h3 : Nat.card (Set.range ψ) ≤ Nat.card (Fin n × H) :=
    Nat.card_le_card_of_surjective (fun p => (⟨ψ p, p, rfl⟩ : Set.range ψ))
      (fun ⟨_, p, hp⟩ => ⟨p, Subtype.ext hp⟩)
  calc Nat.card (Subgroup.closure A) ≤ Nat.card (Set.range ψ) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card (Fin n × H) := h3
    _ = n * Nat.card H := h2

theorem card_closure_le_chain [Finite G] (s : ℕ → G) (f : ℕ → ℕ) (n : ℕ → ℕ) (t : ℕ → ℕ → G)
    (hf : ∀ i, f i ≤ f (i + 1)) (ht : ∀ i ≥ 3, ∀ k, t i k = 1)
    (h1 : ∀ i < 3, ∃ k < n i, t i k = 1)
    (hm : ∀ i < 3, ∀ k < n i, t i k ∈ Subgroup.closure (s '' {j | f i ≤ j ∧ j < f 3}))
    (hc : ∀ i < 3, ∀ j, f i ≤ j → j < f 3 → ∀ k < n i, ∃ k' < n i, ∃ c₁ < n (i + 1),
      ∃ c₂ < n (i + 2), s j * t i k = t i k' * (t (i + 1) c₁ * t (i + 2) c₂)) :
    Nat.card (Subgroup.closure (s '' {j | f 0 ≤ j ∧ j < f 3})) ≤ n 0 * n 1 * n 2 := by
  let C : ℕ → Subgroup G := fun i => Subgroup.closure (s '' {j | f i ≤ j ∧ j < f 3})
  have hfmono : ∀ i d, f i ≤ f (i + d) := by
    intro i d
    induction d with
    | zero => exact le_refl _
    | succ d ih => exact ih.trans (hf _)
  have hCmono : ∀ i d, C (i + d) ≤ C i := by
    intro i d
    refine Subgroup.closure_mono (Set.image_mono fun j hj => ⟨?_, hj.2⟩)
    exact (hfmono i d).trans hj.1
  have hC3 : Nat.card (C 3) = 1 := by
    have : C 3 = ⊥ := by
      refine Subgroup.closure_eq_bot_iff.2 ?_
      rintro _ ⟨j, hj, rfl⟩
      exact absurd hj.2 (not_lt.2 hj.1)
    rw [this, Subgroup.card_bot]
  have htC : ∀ i k, (i < 3 → k < n i) → t i k ∈ C i := by
    intro i k hk
    by_cases hi : i < 3
    · exact hm i hi k (hk hi)
    · rw [ht i (by omega) k]
      exact (C i).one_mem
  have step : ∀ i < 3, Nat.card (C i) ≤ n i * Nat.card (C (i + 1)) := by
    intro i hi
    refine card_closure_le _ (C (i + 1)) (n i) (t i) (h1 i hi) ?_
    rintro _ ⟨j, hj, rfl⟩ k hk
    obtain ⟨k', hk', c₁, hc₁, c₂, hc₂, e⟩ := hc i hi j hj.1 hj.2 k hk
    refine ⟨k', hk', t (i + 1) c₁ * t (i + 2) c₂, ?_, e⟩
    have hn1 : (i + 1 < 3 → c₁ < n (i + 1)) := fun _ => hc₁
    have hn2 : (i + 2 < 3 → c₂ < n (i + 2)) := fun _ => hc₂
    exact (C (i + 1)).mul_mem (htC _ _ hn1) (hCmono (i + 1) 1 (htC _ _ hn2))
  have s0 := step 0 (by decide)
  have s1 := step 1 (by decide)
  have s2 := step 2 (by decide)
  change Nat.card (C 0) ≤ n 0 * n 1 * n 2
  calc Nat.card (C 0) ≤ n 0 * Nat.card (C 1) := s0
    _ ≤ n 0 * (n 1 * Nat.card (C 2)) := Nat.mul_le_mul_left _ s1
    _ ≤ n 0 * (n 1 * (n 2 * Nat.card (C 3))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ s2)
    _ = n 0 * n 1 * n 2 := by rw [hC3, Nat.mul_one, Nat.mul_assoc]

end CFSG.EvenSporadicStandard.Co1Pair
