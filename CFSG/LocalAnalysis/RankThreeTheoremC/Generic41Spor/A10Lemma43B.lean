module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43BCent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup A10B123

theorem a10y_B123 {Y : Type} [Group Y] [Finite Y] {J₁ J₂ : Subgroup Y} {t₁ t₂ : Y}
    (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hA₁ : Nonempty (↥J₁ ⧸ primeComplementCore (G := ↥J₁) 5 ≃* alternatingGroup (Fin 5)))
    (hA₂ : Nonempty (↥J₂ ⧸ primeComplementCore (G := ↥J₂) 5 ≃* alternatingGroup (Fin 5)))
    (ht₁ : t₁ ∈ J₁) (ht₂ : t₂ ∈ J₂) (ho₁ : orderOf t₁ = 5) (ho₂ : orderOf t₂ = 5)
    {W : Subgroup Y} (hW : IsPGroup 2 W) (hd : t₁ * t₂ ∈ Subgroup.normalizer (W : Set Y)) :
    W ≤ Subgroup.normalizer ((zpowers t₁ ⊔ zpowers t₂ : Subgroup Y) : Set Y) := by
  obtain ⟨Q₁⟩ := a5Quot_of_component hJ₁ hA₁
  obtain ⟨Q₂⟩ := a5Quot_of_component hJ₂ hA₂
  have hdc := W_centralizes hJ₁ hJ₂ hne Q₁ Q₂ ht₁ ht₂ ho₁ ho₂ hW hd
  rw [Subgroup.le_normalizer_iff]
  intro y hy k hk
  obtain ⟨h₁, h₂⟩ := conj_mem_P hJ₁ hJ₂ hne Q₁ Q₂ ht₁ ht₂ ho₁ ho₂ (hdc y hy)
  exact conj_mem_P_of_gens h₁ h₂ k hk

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
