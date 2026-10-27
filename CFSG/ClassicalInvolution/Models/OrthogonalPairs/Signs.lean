module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Main

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.WeakCT

variable {K K' V : Type} [Field K] [Finite K] [Field K'] [Finite K'] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p f : ℕ} [Fact p.Prime]
  [CharP K' p] {L₁ L₂ L₃ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ i₃ : V ≃ₗ[K] V}

omit [Finite K] in
theorem linearBlockStandardPair_swap {X : Type} [Group X] {W U V : Subgroup X}
    (h : LinearBlockStandardPair K W U V) : LinearBlockStandardPair K W V U := by
  obtain ⟨θ, c, hr, hk, h1 | h1⟩ := h
  · exact ⟨θ, c, hr, hk, Or.inr h1⟩
  · exact ⟨θ, c, hr, hk, Or.inl h1⟩

theorem unitaryBlockStandardPair_swap {X : Type} [Group X] {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair K' p f W U V) : UnitaryBlockStandardPair K' p f W V U := by
  obtain ⟨θ, c, hr, hk, h1 | h1⟩ := h
  · exact ⟨θ, c, hr, hk, Or.inr h1⟩
  · exact ⟨θ, c, hr, hk, Or.inl h1⟩

theorem lemma_6_11_signs (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂)
    (h₃ : IsFundamental Q L₃ i₃) (h₁₂ : i₁ * i₂ = i₂ * i₁) (h₃₂ : i₃ * i₂ = i₂ * i₃)
    (h₁₃ : i₁ * i₃ = i₃ * i₁) (hL : ∀ x ∈ L₁, ∀ y ∈ L₃, x * y = y * x)
    (hN₁ : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hN₃ : i₂ ∈ Subgroup.normalizer (L₃ : Set (V ≃ₗ[K] V)))
    (hC₁ : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC₃ : i₂ ∉ Subgroup.centralizer (L₃ : Set (V ≃ₗ[K] V))) :
    (HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
        HasSingularVector Q (negSpace i₂ ⊓ negSpace i₃) ∧
        LinearBlockStandardPair K (L₁ ⊔ L₂) L₁ L₂ ∧
        LinearBlockStandardPair K (L₂ ⊔ L₃) L₂ L₃) ∨
      (¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
        ¬ HasSingularVector Q (negSpace i₂ ⊓ negSpace i₃) ∧
        UnitaryBlockStandardPair K' p f (L₁ ⊔ L₂) L₁ L₂ ∧
        UnitaryBlockStandardPair K' p f (L₂ ⊔ L₃) L₂ L₃) := by
  have hiff := lemma_6_11 hodd h₁ h₂ h₃ h₁₂ h₃₂ h₁₃ hL hN₁ hN₃ hC₁ hC₃
  obtain ⟨-, hd₁₂⟩ := lemma_6_10_dichotomy hK hK' hodd h₁ h₂ h₁₂ hN₁ hC₁
  obtain ⟨-, hd₃₂⟩ := lemma_6_10_dichotomy hK hK' hodd h₃ h₂ h₃₂ hN₃ hC₃
  rw [inf_comm (negSpace i₃) (negSpace i₂), sup_comm L₃ L₂] at hd₃₂
  rcases hd₁₂ with ⟨hs₁, hl₁⟩ | ⟨hs₁, hu₁⟩
  · rcases hd₃₂ with ⟨hs₃, hl₃⟩ | ⟨hs₃, -⟩
    · exact Or.inl ⟨hs₁, hs₃, hl₁, linearBlockStandardPair_swap hl₃⟩
    · exact absurd (hiff.mp hs₁) hs₃
  · rcases hd₃₂ with ⟨hs₃, -⟩ | ⟨hs₃, hu₃⟩
    · exact absurd (hiff.mpr hs₃) hs₁
    · exact Or.inr ⟨hs₁, hs₃, hu₁, unitaryBlockStandardPair_swap hu₃⟩

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
