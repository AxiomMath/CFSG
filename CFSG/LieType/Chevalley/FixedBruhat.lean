module

public import Mathlib

public section

namespace CFSG.LieType.Chevalley

variable {G W : Type*} [Group G] [Group W]

theorem exists_fixed_mul_of_fixed (B N : Subgroup G) (φ : N →* W) (n : W → G) (U : W → Set G)
    (F : G ≃* G) (δ : W ≃* W)
    (hcover : ∀ g : G, ∃ m : N, ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * (m : G) * b₂)
    (hdisj : ∀ m m' : N, ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ b₃ ∈ B, ∀ b₄ ∈ B,
      b₁ * (m : G) * b₂ = b₃ * (m' : G) * b₄ → φ m = φ m')
    (hexists : ∀ m : N, ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∃ b ∈ B, ∃ u ∈ U (φ m),
      b₁ * (m : G) * b₂ = b * n (φ m) * u)
    (hunique : ∀ w, ∀ b ∈ B, ∀ b' ∈ B, ∀ u ∈ U w, ∀ u' ∈ U w,
      b * n w * u = b' * n w * u' → b = b' ∧ u = u')
    (hFB : ∀ b ∈ B, F b ∈ B) (hFN : ∀ m : N, F m ∈ N)
    (hδ : ∀ m : N, φ ⟨F m, hFN m⟩ = δ (φ m)) (hFU : ∀ w, ∀ u ∈ U w, F u ∈ U (δ w))
    (hFn : ∀ w, δ w = w → F (n w) = n w) {g : G} (hg : F g = g) :
    ∃ w, δ w = w ∧ ∃ b ∈ B, F b = b ∧ ∃ u ∈ U w, F u = u ∧ g = b * n w * u := by
  obtain ⟨m, b₁, hb₁, b₂, hb₂, rfl⟩ := hcover g
  have hw : δ (φ m) = φ m := by
    have h := hg
    rw [map_mul, map_mul] at h
    rw [← hδ m]
    exact hdisj _ _ _ (hFB _ hb₁) _ (hFB _ hb₂) _ hb₁ _ hb₂ h
  obtain ⟨b, hb, u, hu, hbu⟩ := hexists m b₁ hb₁ b₂ hb₂
  refine ⟨φ m, hw, b, hb, ?_, u, hu, ?_, hbu⟩
  all_goals
    have h := hg
    rw [hbu, map_mul, map_mul, hFn _ hw] at h
    have hFu : F u ∈ U (φ m) := hw ▸ hFU _ u hu
    have := hunique (φ m) _ (hFB b hb) _ hb _ hFu _ hu h
  · exact this.1
  · exact this.2

end CFSG.LieType.Chevalley
