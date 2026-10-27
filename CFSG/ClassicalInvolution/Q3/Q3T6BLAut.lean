module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open Matrix
open scoped MatrixGroups
open CFSG.ClassicalInvolution.Q3.Q3T6

local notation "𝕄" => Matrix (Fin 2) (Fin 2) (ZMod 3)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1000 in
private theorem laut_aux : ∀ g : Matrix (Fin 2) (Fin 2) (ZMod 3), g.det = 2 →
    (g * g = 1 ∨ g * g = -1) →
    ∀ h₁ : Matrix (Fin 2) (Fin 2) (ZMod 3), h₁.det = 1 → (h₁ * h₁ = 1 ∨ h₁ * h₁ = -1) →
      ¬ (h₁ = 1 ∨ h₁ = -1) → (h₁ * g = g * h₁ ∨ h₁ * g = -(g * h₁)) →
    ∀ h₂ : Matrix (Fin 2) (Fin 2) (ZMod 3), h₂.det = 1 → (h₂ * h₂ = 1 ∨ h₂ * h₂ = -1) →
      ¬ (h₂ = 1 ∨ h₂ = -1) → (h₂ * g = g * h₂ ∨ h₂ * g = -(g * h₂)) →
        h₁ = h₂ ∨ h₁ = -h₂ := by
  decide +kernel

private theorem gl_center_iff' (g : GL (Fin 2) (ZMod 3)) :
    conjAut g = 1 ↔ g = 1 ∨ g = -1 := by
  rw [← MonoidHom.mem_ker, conjAut3_ker, Aut.mem_center_gl3_iff]

private theorem gl_eq_or_neg_iff (u v : GL (Fin 2) (ZMod 3)) :
    (u = v ∨ u = -v) ↔ ((u : 𝕄) = v ∨
      (u : 𝕄) = -v) := by
  constructor
  · rintro (h | h)
    · left
      rw [h]
    · right
      rw [h]
      simp
  · rintro (h | h)
    · left
      exact Units.ext h
    · right
      exact Units.ext (by simpa using h)

theorem eq_of_commuting_involutions_inn3 (τ α₁ α₂ : MulAut SL(2, ZMod 3)) (hτ2 : τ * τ = 1)
    (hτ : τ ∉ inn3) (hα₁ : α₁ ∈ inn3) (hα₂ : α₂ ∈ inn3) (h₁2 : α₁ * α₁ = 1)
    (h₂2 : α₂ * α₂ = 1) (h₁ : α₁ ≠ 1) (h₂ : α₂ ≠ 1) (c₁ : α₁ * τ = τ * α₁)
    (c₂ : α₂ * τ = τ * α₂) : α₁ = α₂ := by
  obtain ⟨g, rfl⟩ := conjAut3_surjective τ
  obtain ⟨b₁, rfl⟩ := hα₁
  obtain ⟨b₂, rfl⟩ := hα₂
  rw [← conjAut_toGL b₁] at h₁2 h₁ c₁
  rw [← conjAut_toGL b₂] at h₂2 h₂ c₂
  rw [← conjAut_toGL b₁, ← conjAut_toGL b₂]
  set k₁ : GL (Fin 2) (ZMod 3) := Matrix.SpecialLinearGroup.toGL b₁ with hk₁
  set k₂ : GL (Fin 2) (ZMod 3) := Matrix.SpecialLinearGroup.toGL b₂ with hk₂
  have hdetg : (g : 𝕄).det = 2 := by
    have hu : GeneralLinearGroup.det g ≠ 1 := by
      intro h1
      apply hτ
      have hmem : g ∈ (GeneralLinearGroup.det : GL (Fin 2) (ZMod 3) →* (ZMod 3)ˣ).ker := h1
      rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hmem
      obtain ⟨b, hb⟩ := hmem
      rw [← hb, conjAut_toGL]
      exact conj_mem_inn3 b
    have hcases : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1 := by decide
    rcases hcases (GeneralLinearGroup.det g) with h | h
    · exact absurd h hu
    · have := Matrix.GeneralLinearGroup.val_det_apply g
      rw [h] at this
      rw [← this]
      decide
  have hdet1 : (k₁ : 𝕄).det = 1 := b₁.2
  have hdet2 : (k₂ : 𝕄).det = 1 := b₂.2
  have hg2 : (g : 𝕄) * g = 1 ∨ (g : 𝕄) * g = -1 := by
    have h1 : g * g = 1 ∨ g * g = -1 := by
      rw [← gl_center_iff', map_mul]
      exact hτ2
    rcases h1 with h' | h'
    · left
      simpa using congrArg Units.val h'
    · right
      simpa using congrArg Units.val h'
  have hsq : ∀ k : GL (Fin 2) (ZMod 3), conjAut k * conjAut k = 1 →
      ((k : 𝕄) * k = 1 ∨ (k : 𝕄) * k = -1) := by
    intro k hk
    have h1 : k * k = 1 ∨ k * k = -1 := by
      rw [← gl_center_iff', map_mul]
      exact hk
    rcases h1 with h' | h'
    · left
      simpa using congrArg Units.val h'
    · right
      simpa using congrArg Units.val h'
  have hne1 : ∀ k : GL (Fin 2) (ZMod 3), conjAut k ≠ 1 →
      ¬ ((k : 𝕄) = 1 ∨ (k : 𝕄) = -1) := by
    intro k hk hcon
    apply hk
    rw [gl_center_iff']
    rcases hcon with h' | h'
    · left
      exact Units.ext (by simpa using h')
    · right
      exact Units.ext (by simpa using h')
  have hcm : ∀ k : GL (Fin 2) (ZMod 3), conjAut k * conjAut g = conjAut g * conjAut k →
      ((k : 𝕄) * g = g * k ∨
        (k : 𝕄) * g = -(g * k)) := by
    intro k hk
    have h1 : conjAut (k * g) = conjAut (g * k) := by
      rw [map_mul, map_mul]
      exact hk
    have h1' : conjAut ((g * k)⁻¹ * (k * g)) = 1 := by
      rw [map_mul, map_inv, h1]
      exact inv_mul_cancel _
    rcases (gl_center_iff' _).mp h1' with h2 | h2
    · left
      have : k * g = g * k := by
        calc k * g = (g * k) * ((g * k)⁻¹ * (k * g)) := by group
          _ = g * k := by rw [h2, mul_one]
      simpa using congrArg Units.val this
    · right
      have : k * g = -(g * k) := by
        calc k * g = (g * k) * ((g * k)⁻¹ * (k * g)) := by group
          _ = -(g * k) := by rw [h2, mul_neg, mul_one]
      simpa using congrArg Units.val this
  have key := laut_aux _ hdetg hg2 _ hdet1 (hsq k₁ h₁2) (hne1 k₁ h₁) (hcm k₁ c₁) _ hdet2
    (hsq k₂ h₂2) (hne1 k₂ h₂) (hcm k₂ c₂)
  have hfin : k₁ = k₂ ∨ k₁ = -k₂ := by
    rw [gl_eq_or_neg_iff]
    exact key
  rcases hfin with h' | h'
  · rw [h']
  · rw [h']
    have h0 : conjAut (-1 : GL (Fin 2) (ZMod 3)) = 1 := (gl_center_iff' _).mpr (Or.inr rfl)
    calc conjAut (-k₂) = conjAut ((-1) * k₂) := by rw [neg_one_mul]
      _ = conjAut k₂ := by rw [map_mul, h0, one_mul]

end CFSG.ClassicalInvolution.Q3.Q3T6B
