module

public import CFSG.LocalAnalysis.ABGTheoremB.IV4

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

structure IVNFacts : Prop where
  L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G)
  C_odd_le_oddCore : ∀ c ∈ σ.C, Odd (orderOf c) → c ∈ oddCoreIn σ.C
  C_le_oddCore_sup_D : σ.C ≤ oddCoreIn σ.C ⊔ σ.D
  N_mod_L_cyclic : ∃ g ∈ σ.N, ∀ n ∈ σ.N, ∃ k : ℤ, n * (g ^ k)⁻¹ ∈ σ.L
  C_inf_L_commutator : ⁅σ.C ⊓ σ.L, σ.C ⊓ σ.L⁆ ≤ solvRadIn σ.L
  exists_inverting_D_L₀ : ∃ d ∈ σ.D, d ∈ σ.L₀ ∧
    ∀ c ∈ σ.C ⊓ σ.L₀, Odd (orderOf c) → d * c * d⁻¹ * c ∈ σ.ON
  C_inf_L₀_commutator : ⁅σ.C ⊓ σ.L₀, σ.C ⊓ σ.L₀⁆ ≤ σ.ON
  center_le_L_or_inf_L_le : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ P : Subgroup G,
    IsSylowOf r P σ.C → σ.D ≤ Subgroup.normalizer (P : Set G) →
      centerOf P ≤ σ.L ∨ P ⊓ σ.L ≤ σ.ON
  centralizer_SL2_section : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ P : Subgroup G,
    IsSylowOf r P σ.C → σ.D ≤ Subgroup.normalizer (P : Set G) → ¬ centerOf P ≤ σ.L₀ →
      P ⊓ σ.L ≤ σ.ON →
        ∃ Λ : Subgroup G, (∀ l : G, l ∈ Λ ↔ l ∈ σ.L₀ ∧ ∀ g ∈ P, g * l * g⁻¹ * l⁻¹ ∈ σ.ON) ∧
          ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (m : ℕ), 1 < m ∧ Odd m ∧
            σ.q = Nat.card F₀ ^ m ∧ ∃ φ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F₀,
              Function.Surjective φ ∧ φ.ker = σ.ON.subgroupOf Λ
  L_centralizer_D_odd_le : ∀ y ∈ σ.L, y ∈ Subgroup.centralizer (σ.D : Set G) →
    Odd (orderOf y) → y ∈ σ.ON
  frobenius_section : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ w ∈ Subgroup.centralizer (σ.D : Set G),
    (∃ n : ℕ, w ^ p ^ n = 1) → w ∉ σ.L → w ^ p ∈ σ.ON → ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ p ∧
      ∃ K₀ : Subgroup G, σ.ON ≤ K₀ ∧ K₀ ≤ σ.N ∧ σ.ON.relIndex K₀ = s ∧
        w ∈ Subgroup.normalizer (K₀ : Set G) ∧ (∀ k ∈ K₀, σ.x₂ * k * σ.x₂⁻¹ * k ∈ σ.ON) ∧
        ∀ k ∈ K₀, w * k * w⁻¹ * k⁻¹ ∈ σ.ON → k ∈ σ.ON
  oddCore_C_inf_L₀_cyclic : ∃ g ∈ σ.N, oddCoreIn σ.C ⊓ σ.L₀ ≤ Subgroup.zpowers g ⊔ σ.ON
  oddCore_C_inf_L₀_coprime : ¬ σ.p ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀)
  oddCore_C_inf_L₀_centralized : ∀ c ∈ σ.D ⊓ Subgroup.centralizer (σ.T : Set G),
    ∀ k ∈ oddCoreIn σ.C ⊓ σ.L₀, c * k * c⁻¹ * k⁻¹ ∈ σ.ON
  oddCore_C_inf_L₀_inverted : ∃ d ∈ σ.D, d ∉ Subgroup.centralizer (σ.T : Set G) ∧
    ∀ k ∈ oddCoreIn σ.C ⊓ σ.L₀, d * k * d⁻¹ * k ∈ σ.ON
  sylow_quaternion_element : ∃ y ∈ (σ.S : Subgroup G), y ∉ centerOf (σ.S : Subgroup G) ∧
    ∀ X : Subgroup G, X ≤ σ.S → (σ.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
      (∃ Q : Subgroup G, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) → y ∈ X
  propIV51 : σ.PropIV51

end Setting

end CFSG.ABGTheoremB
