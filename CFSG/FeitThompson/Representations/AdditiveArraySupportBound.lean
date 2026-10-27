module

public import Mathlib.Data.Set.Card
public import Mathlib.Basic.Complex.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

theorem min_le_ncard_support_of_add_swap {M : Type*} [AddZeroClass M] {ι κ : Type*} [Finite ι]
    [Finite κ] (a : ι → κ → M) (hrect : ∀ i k : ι, ∀ j l : κ, a i j + a k l = a i l + a k j)
    (ha : ∃ i j, a i j ≠ 0) :
    min (Nat.card ι) (Nat.card κ) ≤ {p : ι × κ | a p.1 p.2 ≠ 0}.ncard := by
  classical
  obtain ⟨i₀, j₀, hij⟩ := ha
  set S : Set (ι × κ) := {p | a p.1 p.2 ≠ 0} with hS
  have hfin : S.Finite := Set.toFinite _
  by_cases hrow : ∀ j, a i₀ j ≠ 0
  ·
    have hsub : Set.range (fun j : κ => ((i₀, j) : ι × κ)) ⊆ S := by
      rintro p ⟨j, rfl⟩
      exact hrow j
    have hinj : Function.Injective (fun j : κ => ((i₀, j) : ι × κ)) := by
      intro j j' h
      simpa using h
    have hle := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_range_of_injective hinj] at hle
    exact le_trans (min_le_right _ _) hle
  ·
    push Not at hrow
    obtain ⟨l, hl⟩ := hrow
    have key : ∀ k, a k j₀ ≠ 0 ∨ a k l ≠ 0 := by
      intro k
      by_contra h
      push Not at h
      obtain ⟨h1, h2⟩ := h
      have h3 := hrect i₀ k j₀ l
      rw [h1, h2, hl] at h3
      exact hij (by simpa using h3)
    set f : ι → ι × κ := fun k => if a k j₀ = 0 then (k, l) else (k, j₀) with hf
    have hfst : ∀ k, (f k).1 = k := by
      intro k
      by_cases h : a k j₀ = 0 <;> simp [hf, h]
    have hsub : Set.range f ⊆ S := by
      rintro p ⟨k, rfl⟩
      by_cases h : a k j₀ = 0
      · have := (key k).resolve_left (by simp [h])
        simpa [hf, h, hS] using this
      · simp [hf, h, hS]
    have hinj : Function.Injective f := by
      intro k k' h
      have := congrArg Prod.fst h
      rwa [hfst, hfst] at this
    have hle := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_range_of_injective hinj] at hle
    exact le_trans (min_le_left _ _) hle

theorem min_le_ncard_support_of_add_swap_fin {m n : ℕ} (a : Fin m → Fin n → ℂ)
    (hrect : ∀ i k : Fin m, ∀ j l : Fin n, a i j + a k l = a i l + a k j) (ha : a ≠ 0) :
    min m n ≤ {p : Fin m × Fin n | a p.1 p.2 ≠ 0}.ncard := by
  have ha' : ∃ i j, a i j ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext fun i => funext fun j => h i j)
  simpa using min_le_ncard_support_of_add_swap a hrect ha'

theorem min_le_card_filter_support_of_add_swap {m n : ℕ} (a : Fin m → Fin n → ℂ)
    (hrect : ∀ i k : Fin m, ∀ j l : Fin n, a i j + a k l = a i l + a k j) (ha : a ≠ 0) :
    min m n ≤ #{p : Fin m × Fin n | a p.1 p.2 ≠ 0} := by
  classical
  have := min_le_ncard_support_of_add_swap_fin a hrect ha
  rwa [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] at this

end CFSG.FeitThompson
