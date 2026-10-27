module

public import CFSG.LocalAnalysis.GH72.Sec5Roles

public section

namespace CFSG.GH72

open Subgroup G5d

namespace Sec5ConfigTR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  {𝔠 : Sec5ConfigR ρ p} (𝔱 : Sec5ConfigTR 𝔠)

theorem lemma_5_17_of
    (h52 : ((∃ H, CFSG.IsPLocal 𝔱.t H ∧ A ≤ H ∧ Covers H ρ.M₀ (O ρ.M) ∧
        Sec4Setting.PConstrainedWrt 𝔱.t A H ρ.Y) →
      ∀ P, IsMaxInvIn 𝔱.t A ⊤ P →
        ρ.IsCoveringFirst 𝔱.t (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          Sec4Setting.PConstrainedWrt 𝔱.t A (normalizer (CFSG.ambientMaxCardZJ P : Set G))
            ρ.Y) ∧
      ((∃ H, CFSG.IsPLocal 𝔱.t H ∧ A ≤ H ∧ Covers H ρ.N₀ (O ρ.N) ∧
        Sec4Setting.PConstrainedWrt 𝔱.t A H ρ.X) →
      ∀ P, IsMaxInvIn 𝔱.t A ⊤ P →
        ρ.IsCoveringSecond 𝔱.t (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          Sec4Setting.PConstrainedWrt 𝔱.t A (normalizer (CFSG.ambientMaxCardZJ P : Set G))
            ρ.X))
    (h515 : 𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥ →
      Sec4Setting.PConstrainedWrt 𝔱.t A (C 𝔱.x₁) ρ.Y)
    (h516 : 𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥ →
      ∃ y₁ ∈ ρ.Y, y₁ ≠ 1 ∧ Sec4Setting.PConstrainedWrt 𝔱.t A (C y₁) ρ.X)
    (h : 𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥) (Tt : Subgroup G)
    (hTt : IsMaxInvIn 𝔱.t A ⊤ Tt) :
    ρ.IsCovering 𝔱.t (normalizer (CFSG.ambientMaxCardZJ Tt : Set G)) := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => ρ.comm ha hb
  obtain ⟨H₁, hH₁, hAH₁, hcov₁, hc₁⟩ := exists_pLocal_covers_of_pConstrainedWrt 𝔱.ht.1
    𝔱.ht.2.1 ρ.isPGroup_A hAc ρ.X_le_A 𝔱.hx₁.1 ρ.M₀_le ρ.O_M_le_M₀ (h515 h)
  obtain ⟨y₁, hy₁, -, hCy₁⟩ := h516 h
  obtain ⟨H₂, hH₂, hAH₂, hcov₂, hc₂⟩ := exists_pLocal_covers_of_pConstrainedWrt 𝔱.ht.1
    𝔱.ht.2.1 ρ.isPGroup_A hAc ρ.Y_le_A hy₁ ρ.N₀_le ρ.O_N_le_N₀ hCy₁
  obtain ⟨hfirst, -⟩ := h52.1 ⟨H₁, hH₁, hAH₁, hcov₁, hc₁⟩ Tt hTt
  obtain ⟨hsecond, -⟩ := h52.2 ⟨H₂, hH₂, hAH₂, hcov₂, hc₂⟩ Tt hTt
  exact ⟨hfirst.1, hfirst.2, hsecond.2⟩

end Sec5ConfigTR

end CFSG.GH72
