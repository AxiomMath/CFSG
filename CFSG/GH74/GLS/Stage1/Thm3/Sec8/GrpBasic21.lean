module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

theorem no_invol_coset {G : Type*} [Group G] {P₁ P₂ : Subgroup G} {z y : G}
    (hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    (hinf : ∀ x, x ∈ P₁ → x ∈ P₂ → x = 1 ∨ x = z)
    (hzP₁ : z ∈ P₁) (hzP₂ : z ∈ P₂) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hy2 : y * y = z)
    (hy12 : ∀ p ∈ P₁, y * p * y⁻¹ ∈ P₂) (hy21 : ∀ p ∈ P₂, y * p * y⁻¹ ∈ P₁) :
    ∀ p ∈ P₁ ⊔ P₂, (p * y) * (p * y) ≠ 1 := by
  intro p hp hpy
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := mem_sup_of_commute' hcomm hp
  have hzc₂ : ∀ b ∈ P₂, z * b = b * z := fun b hb => hcomm z hzP₁ b hb
  have hs₁ : y * p₁ * y⁻¹ ∈ P₂ := hy12 p₁ hp₁
  have hs₂ : y * p₂ * y⁻¹ ∈ P₁ := hy21 p₂ hp₂
  obtain ⟨s₁, hs₁def⟩ : ∃ s₁ : G, s₁ = y * p₁ * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂def⟩ : ∃ s₂ : G, s₂ = y * p₂ * y⁻¹ := ⟨_, rfl⟩
  rw [← hs₁def] at hs₁
  rw [← hs₂def] at hs₂
  have hσσ : y * s₂ * y⁻¹ = p₂ := by
    rw [hs₂def]
    calc y * (y * p₂ * y⁻¹) * y⁻¹ = (y * y) * p₂ * (y * y)⁻¹ := by group
      _ = z * p₂ * z⁻¹ := by rw [hy2]
      _ = p₂ := by rw [hzc₂ p₂ hp₂]; group
  have hyz : y * z * y⁻¹ = z := by
    calc y * z * y⁻¹ = y * (y * y) * y⁻¹ := by rw [hy2]
      _ = (y * y) := by group
      _ = z := hy2
  have e1 : (p₁ * p₂ * y) * (p₁ * p₂ * y) = (p₁ * p₂ * s₁ * s₂) * (y * y) := by
    rw [hs₁def, hs₂def]; group
  have e2 : p₁ * p₂ * s₁ * s₂ = z := by
    have h1 : (p₁ * p₂ * s₁ * s₂) * z = 1 := by
      rw [← hy2, ← e1]; exact hpy
    calc p₁ * p₂ * s₁ * s₂ = ((p₁ * p₂ * s₁ * s₂) * z) * z := by rw [mul_assoc _ z z, hz2, mul_one]
      _ = z := by rw [h1, one_mul]
  have e3 : p₁ * p₂ * s₁ * s₂ = (p₁ * s₂) * (p₂ * s₁) := by
    have c1 : s₁ * s₂ = s₂ * s₁ := (hcomm s₂ hs₂ s₁ hs₁).symm
    have c2 : p₂ * s₂ = s₂ * p₂ := (hcomm s₂ hs₂ p₂ hp₂).symm
    calc p₁ * p₂ * s₁ * s₂ = p₁ * (p₂ * (s₁ * s₂)) := by group
      _ = p₁ * (p₂ * (s₂ * s₁)) := by rw [c1]
      _ = p₁ * ((p₂ * s₂) * s₁) := by group
      _ = p₁ * ((s₂ * p₂) * s₁) := by rw [c2]
      _ = (p₁ * s₂) * (p₂ * s₁) := by group
  have hq : (p₁ * s₂) * (p₂ * s₁) = z := by rw [← e3]; exact e2
  have hq₂ : p₂ * s₁ ∈ P₂ := mul_mem hp₂ hs₁
  have hq₁ : p₁ * s₂ ∈ P₁ := mul_mem hp₁ hs₂
  have hq₁' : p₁ * s₂ = z * (p₂ * s₁)⁻¹ := eq_mul_inv_of_mul_eq hq
  have hq₁P₂ : p₁ * s₂ ∈ P₂ := by rw [hq₁']; exact mul_mem hzP₂ (inv_mem hq₂)
  have hs₂eq : s₂ = p₁⁻¹ * (p₁ * s₂) := by group
  have hp₂eq : p₂ = (y * p₁ * y⁻¹)⁻¹ * (y * (p₁ * s₂) * y⁻¹) := by
    have : p₂ = y * s₂ * y⁻¹ := hσσ.symm
    rw [this, hs₂eq]
    group
  rcases hinf _ hq₁ hq₁P₂ with h0 | h0
  · apply hz1
    rw [h0] at hp₂eq hq
    have hp₂' : p₂ = s₁⁻¹ := by
      rw [hp₂eq, ← hs₁def]; group
    rw [hp₂'] at hq
    rw [← hq]
    group
  · apply hz1
    rw [h0] at hp₂eq hq
    have hp₂' : p₂ = s₁⁻¹ * z := by
      rw [hp₂eq, ← hs₁def]
      calc s₁⁻¹ * (y * z * y⁻¹) = s₁⁻¹ * z := by rw [hyz]
        _ = s₁⁻¹ * z := rfl
    have hzs₁ : z * s₁ = s₁ * z := hzc₂ s₁ hs₁
    have : p₂ * s₁ = z := by
      rw [hp₂']
      calc s₁⁻¹ * z * s₁ = s₁⁻¹ * (z * s₁) := by group
        _ = s₁⁻¹ * (s₁ * z) := by rw [hzs₁]
        _ = z := by group
    rw [this] at hq
    rw [hz2] at hq
    exact hq.symm

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
