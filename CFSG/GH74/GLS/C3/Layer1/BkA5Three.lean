module

public import CFSG.GH74.GLS.C3.Layer1.BkA5Facts

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Equiv Equiv.Perm Subgroup

@[expose] def a5Three : Perm (Fin 5) := swap 1 2 * swap 2 3

theorem a5Three_sign : sign a5Three = 1 := by decide +kernel

theorem a5Three_normalizes : ∀ i : Fin 4, ∃ j : Fin 4, a5Three * a5V i * a5Three⁻¹ = a5V j := by
  decide +kernel

theorem a5Three_ne : ∀ i : Fin 4, a5Three ≠ a5V i := by decide +kernel

theorem normalizer_V_model : ∀ τ : Perm (Fin 5), sign τ = 1 →
    (∀ i : Fin 4, ∃ j : Fin 4, τ * a5V i * τ⁻¹ = a5V j) →
    (∃ i : Fin 4, τ = a5V i) ∨
      (τ ^ 3 = 1 ∧ ∀ i : Fin 4, τ * a5V i * τ⁻¹ = a5V i → a5V i = 1) := by
  decide +kernel


theorem exists_normalizing_not_mem {X : Subgroup (alternatingGroup (Fin 5))} (hX : Nat.card ↥X = 4) :
    ∃ g : alternatingGroup (Fin 5), (∀ y ∈ X, g * y * g⁻¹ ∈ X) ∧ g ∉ X := by
  obtain ⟨c, hcY, hcX⟩ := exists_conj_model5 hX
  let g₀ : alternatingGroup (Fin 5) := ⟨a5Three, (mem_alternatingGroup).2 a5Three_sign⟩
  refine ⟨c * g₀ * c⁻¹, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := hcX y hy
    obtain ⟨j, hj⟩ := a5Three_normalizes i
    have hmem : g₀ * (c⁻¹ * y * c) * g₀⁻¹ ∈ a5Sub := by
      refine ⟨j, ?_⟩
      show a5V j = a5Three * (c⁻¹ * y * c).1 * a5Three⁻¹
      rw [← hi]
      exact hj.symm
    have h2 := hcY _ hmem
    have e : c * (g₀ * (c⁻¹ * y * c) * g₀⁻¹) * c⁻¹ = c * g₀ * c⁻¹ * y * (c * g₀ * c⁻¹)⁻¹ := by
      group
    rwa [e] at h2
  · intro hg
    have h2 := hcX _ hg
    have e : c⁻¹ * (c * g₀ * c⁻¹) * c = g₀ := by group
    rw [e] at h2
    obtain ⟨i, hi⟩ := h2
    exact a5Three_ne i (by simpa [g₀] using hi.symm)

theorem normalizer_X_cases {X : Subgroup (alternatingGroup (Fin 5))} (hX : Nat.card ↥X = 4)
    (σ : alternatingGroup (Fin 5)) (hσ : ∀ y ∈ X, σ * y * σ⁻¹ ∈ X) :
    σ ∈ X ∨ (σ ^ 3 = 1 ∧ ∀ y ∈ X, σ * y * σ⁻¹ = y → y = 1) := by
  obtain ⟨c, hcY, hcX⟩ := exists_conj_model5 hX
  set τ : alternatingGroup (Fin 5) := c⁻¹ * σ * c with hτ
  have hστ : σ = c * τ * c⁻¹ := by rw [hτ]; group
  have hτn : ∀ z ∈ a5Sub, τ * z * τ⁻¹ ∈ a5Sub := by
    intro z hz
    have h1 := hσ _ (hcY z hz)
    have h2 := hcX _ h1
    have e : c⁻¹ * (σ * (c * z * c⁻¹) * σ⁻¹) * c = τ * z * τ⁻¹ := by rw [hτ]; group
    rwa [e] at h2
  have hmodel : ∀ i : Fin 4, ∃ j : Fin 4,
      (τ : Perm (Fin 5)) * a5V i * (τ : Perm (Fin 5))⁻¹ = a5V j := by
    intro i
    have hz : (⟨a5V i, (mem_alternatingGroup).2 (a5V_sign i)⟩ : alternatingGroup (Fin 5)) ∈
        a5Sub := ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hτn _ hz
    exact ⟨j, by simpa using hj.symm⟩
  rcases normalizer_V_model τ (mem_alternatingGroup.1 τ.2) hmodel with ⟨i, hi⟩ | ⟨h3, hfpf⟩
  · left
    have hτmem : τ ∈ a5Sub := ⟨i, hi.symm⟩
    have := hcY _ hτmem
    rwa [← hστ] at this
  · right
    refine ⟨?_, ?_⟩
    · have h3' : τ ^ 3 = 1 := Subtype.ext h3
      rw [hστ, conj_pow, h3']
      group
    · intro y hy hyσ
      obtain ⟨i, hi⟩ := hcX y hy
      have hτy : τ * (c⁻¹ * y * c) * τ⁻¹ = c⁻¹ * y * c := by
        have e : τ * (c⁻¹ * y * c) * τ⁻¹ = c⁻¹ * (σ * y * σ⁻¹) * c := by rw [hτ]; group
        rw [e, hyσ]
      have h1 : (τ : Perm (Fin 5)) * a5V i * (τ : Perm (Fin 5))⁻¹ = a5V i := by
        rw [hi]
        have := congrArg (fun z : alternatingGroup (Fin 5) => (z : Perm (Fin 5))) hτy
        simpa using this
      have h2 := hfpf i h1
      have h3'' : c⁻¹ * y * c = 1 := Subtype.ext (by rw [← hi]; exact h2)
      have : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
      rw [this, h3'']
      group

end CFSG.GH74.GLS.C3.Layer1.Bk
