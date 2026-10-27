module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

namespace E8Fin

open Matrix

abbrev V3 := Fin 3 → ZMod 2

abbrev SL32 := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

@[expose] def w0 : V3 := ![1, 0, 0]

theorem w0_ne_zero : w0 ≠ 0 := by decide

@[expose] def IsK (M : SL32) : Prop := ∀ y : V3, M.1 *ᵥ y = y ∨ M.1 *ᵥ y = y + w0

instance (M : SL32) : Decidable (IsK M) := by unfold IsK; infer_instance

@[expose] def IsT (M : SL32) : Prop := M.1 *ᵥ w0 = w0 ∧ M * M = 1 ∧ M ≠ 1 ∧ ¬ IsK M

instance (M : SL32) : Decidable (IsT M) := by unfold IsT; infer_instance

@[expose] def Sfin : Finset SL32 := Finset.univ.filter fun M => M.1 *ᵥ w0 = w0

@[expose] def Tfin : Finset SL32 := Finset.univ.filter fun M => IsT M

@[expose] def Ts : Finset SL32 := insert 1 Tfin

@[expose] def Kfin : Finset SL32 := Finset.univ.filter fun M => M.1 *ᵥ w0 = w0 ∧ IsK M ∧ M ≠ 1

theorem f_trans : ∀ v w : V3, v ≠ 0 → w ≠ 0 → ∃ M : SL32, M.1 *ᵥ w = v := by
  decide +kernel

theorem f_klein : ∀ A B : SL32, A.1 *ᵥ w0 = w0 → B.1 *ᵥ w0 = w0 → A * A = 1 → B * B = 1 →
    (A * B) * (A * B) = 1 → A ≠ 1 → B ≠ 1 → A * B ≠ 1 → IsK A ∨ IsK B ∨ IsK (A * B) := by
  have h : ∀ A ∈ Sfin, ∀ B ∈ Sfin, A * A = 1 → B * B = 1 →
      (A * B) * (A * B) = 1 → A ≠ 1 → B ≠ 1 → A * B ≠ 1 → IsK A ∨ IsK B ∨ IsK (A * B) := by
    decide +kernel
  intro A B hA hB
  exact h A (by simpa [Sfin] using hA) B (by simpa [Sfin] using hB)

theorem f_fixed : ∀ τ ∈ Kfin, ∃ w₂ : V3, w₂ ≠ 0 ∧ w₂ ≠ w0 ∧ τ.1 *ᵥ w₂ = w₂ := by
  decide +kernel

theorem f_conj : ∀ τ ∈ Kfin, ∀ σ : SL32, ∀ w₂ : V3, w₂ ≠ 0 → w₂ ≠ w0 → τ.1 *ᵥ w₂ = w₂ →
    σ.1 *ᵥ w₂ = w0 → σ.1 *ᵥ w0 ≠ w0 ∧ IsT (σ * τ * σ⁻¹) := by
  decide +kernel

theorem f_T_conj : ∀ t t' : SL32, IsT t → IsT t' →
    ∃ c : SL32, c.1 *ᵥ w0 = w0 ∧ c * t * c⁻¹ = t' := by
  have h : ∀ t ∈ Tfin, ∀ t' ∈ Tfin, ∃ c ∈ Sfin, c * t * c⁻¹ = t' := by decide +kernel
  intro t t' ht ht'
  obtain ⟨c, hc, hct⟩ := h t (by simpa [Tfin] using ht) t' (by simpa [Tfin] using ht')
  exact ⟨c, by simpa [Sfin] using hc, hct⟩

theorem f_T_gen : ∀ s : SL32, s.1 *ᵥ w0 = w0 →
    ∃ t₁ ∈ Ts, ∃ t₂ ∈ Ts, ∃ t₃ ∈ Ts, s = t₁ * t₂ * t₃ := by
  decide +kernel

theorem f_key : ∀ A B : SL32, A.1 *ᵥ w0 = w0 → B.1 *ᵥ w0 = w0 → A * A = 1 → B * B = 1 →
    (A * B) * (A * B) = 1 → A ≠ 1 → B ≠ 1 → A * B ≠ 1 →
    ∃ τ : SL32, (τ = A ∨ τ = B ∨ τ = A * B) ∧ ∃ σ : SL32, σ.1 *ᵥ w0 ≠ w0 ∧
      IsT (σ * τ * σ⁻¹) := by
  intro A B hA hB hA2 hB2 hAB2 hA1 hB1 hAB1
  have hmem : ∀ τ : SL32, τ.1 *ᵥ w0 = w0 → IsK τ → τ ≠ 1 → τ ∈ Kfin := fun τ h1 h2 h3 => by
    simpa [Kfin] using And.intro h1 (And.intro h2 h3)
  have hmain : ∀ τ : SL32, τ ∈ Kfin → ∃ σ : SL32, σ.1 *ᵥ w0 ≠ w0 ∧ IsT (σ * τ * σ⁻¹) := by
    intro τ hτ
    obtain ⟨w₂, hw0, hw1, hτw⟩ := f_fixed τ hτ
    obtain ⟨σ, hσ⟩ := f_trans w0 w₂ w0_ne_zero hw0
    exact ⟨σ, f_conj τ hτ σ w₂ hw0 hw1 hτw hσ⟩
  have hAB : (A * B).1 *ᵥ w0 = w0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB, hA]
  rcases f_klein A B hA hB hA2 hB2 hAB2 hA1 hB1 hAB1 with h | h | h
  · exact ⟨A, Or.inl rfl, hmain A (hmem A hA h hA1)⟩
  · exact ⟨B, Or.inr (Or.inl rfl), hmain B (hmem B hB h hB1)⟩
  · exact ⟨A * B, Or.inr (Or.inr rfl), hmain _ (hmem _ hAB h hAB1)⟩

theorem e8_abs {Γ : Type*} [Group Γ] (ρ : Γ →* SL32) (θ : Γ →* Multiplicative (ZMod 2))
    (hfix : ∀ γ, (ρ γ).1 *ᵥ w0 = w0)
    (hsurj : ∀ M : SL32, M.1 *ᵥ w0 = w0 → ∃ γ, ρ γ = M)
    (hker : ∀ γ, ρ γ = 1 → θ γ = 1) {v : Γ} (hv : IsT (ρ v)) (hθv : θ v = 1) :
    ∀ γ, θ γ = 1 := by
  have hpre : ∀ t ∈ Ts, ∃ δ, ρ δ = t ∧ θ δ = 1 := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨1, map_one _, map_one _⟩
    · have hT : IsT t := by simpa [Tfin] using ht
      obtain ⟨c, hc, hct⟩ := f_T_conj (ρ v) t hv hT
      obtain ⟨γ, rfl⟩ := hsurj c hc
      refine ⟨γ * v * γ⁻¹, ?_, ?_⟩
      · rw [map_mul, map_mul, map_inv]
        exact hct
      · rw [map_mul, map_mul, map_inv, hθv, mul_one, mul_inv_cancel]
  intro γ
  obtain ⟨t₁, h₁, t₂, h₂, t₃, h₃, hγ⟩ := f_T_gen (ρ γ) (hfix γ)
  obtain ⟨δ₁, hδ₁, hθ₁⟩ := hpre t₁ h₁
  obtain ⟨δ₂, hδ₂, hθ₂⟩ := hpre t₂ h₂
  obtain ⟨δ₃, hδ₃, hθ₃⟩ := hpre t₃ h₃
  have hρ : ρ (δ₁ * δ₂ * δ₃)⁻¹ * ρ γ = 1 := by
    rw [map_inv, map_mul, map_mul, hδ₁, hδ₂, hδ₃, hγ]
    exact inv_mul_cancel _
  have h1 := hker ((δ₁ * δ₂ * δ₃)⁻¹ * γ) (by rw [map_mul]; exact hρ)
  have h2 : θ (δ₁ * δ₂ * δ₃) = 1 := by rw [map_mul, map_mul, hθ₁, hθ₂, hθ₃]; rfl
  rw [map_mul, map_inv, h2, inv_one, one_mul] at h1
  exact h1

end E8Fin

end CFSG.ClassicalInvolution.Q3.Sec13
