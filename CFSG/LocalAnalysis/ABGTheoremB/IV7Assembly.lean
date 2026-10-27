module

public import CFSG.LocalAnalysis.ABGTheoremB.IV7Constrained
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Nonconstrained
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Lemma5
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Lemma7
public import CFSG.LocalAnalysis.ABGTheoremB.DGroupNoQ
public import CFSG.LocalAnalysis.ABGTheoremB.IVNFacts
public import CFSG.LocalAnalysis.ABGTheoremB.Statements

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem propIV71_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_C : ∀ c ∈ σ.C, Odd (orderOf c) → c ∈ oddCoreIn σ.C)
    (h_II33 : ∃ g ∈ σ.N, ∀ n ∈ σ.N, ∃ k : ℤ, n * (g ^ k)⁻¹ ∈ σ.L)
    (h_II42 : ⁅σ.C ⊓ σ.L, σ.C ⊓ σ.L⁆ ≤ solvRadIn σ.L)
    (h_II43iii : ∀ y ∈ σ.L, y ∈ Subgroup.centralizer (σ.D : Set G) → Odd (orderOf y) →
      y ∈ σ.ON)
    (h_II43 : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ w ∈ Subgroup.centralizer (σ.D : Set G),
      (∃ n : ℕ, w ^ p ^ n = 1) → w ∉ σ.L → w ^ p ∈ σ.ON → ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ p ∧
        ∃ K₀ : Subgroup G, σ.ON ≤ K₀ ∧ K₀ ≤ σ.N ∧ σ.ON.relIndex K₀ = s ∧
          w ∈ Subgroup.normalizer (K₀ : Set G) ∧ (∀ k ∈ K₀, σ.x₂ * k * σ.x₂⁻¹ * k ∈ σ.ON) ∧
          ∀ k ∈ K₀, w * k * w⁻¹ * k⁻¹ ∈ σ.ON → k ∈ σ.ON)
    (h_II42i : ∃ d ∈ σ.D, d ∈ σ.L₀ ∧
      ∀ c ∈ σ.C ⊓ σ.L₀, Odd (orderOf c) → d * c * d⁻¹ * c ∈ σ.ON)
    (h_II42ii : ⁅σ.C ⊓ σ.L₀, σ.C ⊓ σ.L₀⁆ ≤ σ.ON)
    (h_II42v : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ P : Subgroup G, IsSylowOf r P σ.C →
      σ.D ≤ Subgroup.normalizer (P : Set G) → centerOf P ≤ σ.L ∨ P ⊓ σ.L ≤ σ.ON)
    (h_II42vi : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ P : Subgroup G, IsSylowOf r P σ.C →
      σ.D ≤ Subgroup.normalizer (P : Set G) → ¬ centerOf P ≤ σ.L₀ → P ⊓ σ.L ≤ σ.ON →
        ∃ Λ : Subgroup G, (∀ l : G, l ∈ Λ ↔ l ∈ σ.L₀ ∧ ∀ g ∈ P, g * l * g⁻¹ * l⁻¹ ∈ σ.ON) ∧
          ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (m : ℕ), 1 < m ∧ Odd m ∧
            σ.q = Nat.card F₀ ^ m ∧ ∃ φ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F₀,
              Function.Surjective φ ∧ φ.ker = σ.ON.subgroupOf Λ)
    :
    σ.PropIV71 := by
  intro r hr P R hP hPD hR hRD hRP
  by_cases hc : σ.Constrained r
  · obtain ⟨d, hdP, hdR, -⟩ := σ.exists_IV7Data_of_constrained hσ hII hr hc hP hPD hR hRD hRP
      exists_sylow_not_centralizes_fixed_omega h_L_normal h_C h_II33 h_II42 h_II43iii h_II43
    exact ⟨d, hdP, hdR⟩
  · have h77 := σ.center_le_L₀_of_not_constrained hσ hII hr hc hP hPD hR hRD hRP h_II42v
      h_II42vi σ.isDGroupWrt_no_sl2_section
    obtain ⟨d, hdP, hdR, -⟩ := σ.exists_IV7Data_of_not_constrained hσ hII hr hc hP hPD hR hRD
      hRP h77 h_II42i h_II42ii
    exact ⟨d, hdP, hdR⟩

theorem propIV71_of_IVNFacts (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts) :
    σ.PropIV71 :=
  σ.propIV71_of hσ hII hN.L_normal hN.C_odd_le_oddCore hN.N_mod_L_cyclic hN.C_inf_L_commutator
    hN.L_centralizer_D_odd_le hN.frobenius_section hN.exists_inverting_D_L₀ hN.C_inf_L₀_commutator
    hN.center_le_L_or_inf_L_le hN.centralizer_SL2_section

end Setting

end CFSG.ABGTheoremB
