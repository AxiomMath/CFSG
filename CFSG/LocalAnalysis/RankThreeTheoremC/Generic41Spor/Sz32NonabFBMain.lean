module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem kFactNonabF5_of_parts' (h6 : KFactI6103Five) (h9 : KFactNoM125Sylow') (h714 : KFactI714Four')
    (h10 : KFactFieldGeneration5) (hSz : Sz32Facts) (hSig : Sz32SigOne) :
    ∀ (Y : Type) [Group Y] [Finite Y], CFSG.AGLEmbedding.CatalogSimpleSections Y →
      primeComplementCore (G := Y) 5 = ⊥ →
      ∀ (F Γ B R₀ : Subgroup Y) (x : Y), CFSG.ABGLocalTools.IsSylowOf 5 F ⊤ → ¬ IsMulCommutative F →
        Nat.card F = 125 → (∀ f ∈ F, f ^ 25 = 1) →
        (∀ z ∈ F, (∀ f ∈ F, f * z = z * f) ↔ z ∈ Subgroup.zpowers x) →
        (∀ b, b ∈ B ↔ (b ∈ F ∧ b ^ 5 = 1)) → IsElemAbelian 5 B → Nat.card B = 5 ^ 2 → F ≤ Γ →
        (∀ b ∈ B, b ∉ Subgroup.zpowers x → Subgroup.centralizer ({b} : Set Y) ≤ Γ) →
        R₀ ≠ ⊥ → IsPGroup 2 R₀ → B ≤ Subgroup.normalizer (R₀ : Set Y) →
        GLALayer (⊤ : Subgroup Y) ⊔ pCoreOf 5 (⊤ : Subgroup Y) ≤ Γ := by
  intro Y _ _ hcat hcore F Γ B R₀ x hF hnon hcard hexp hcen hB Belem Bcard hFΓ hC hR hR2 hRn
  have h : NF5 F Γ B R₀ x :=
    ⟨hcat, hcore, hF, hnon, hcard, hexp, hcen, hB, Belem, Bcard, hFΓ, hC, hR, hR2, hRn⟩
  by_cases hex : ∃ L : Subgroup Y, IsComponentOf L ⊤
  · obtain ⟨L, z, hc⟩ := nf5_cfg h6 h hex
    refine sup_le ?_ (nf5_pCoreOf_le h)
    rw [nf5_layer_eq hc]
    exact nf5_L_le h9 h714 h10 hSz hSig hc
  · push Not at hex
    rw [nf5_layer_bot hex, bot_sup_eq]
    exact nf5_pCoreOf_le h

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
