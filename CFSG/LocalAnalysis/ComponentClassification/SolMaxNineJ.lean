module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineI
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineC

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerNineFusionCountInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
    ∀ s ∈ S, s ∉ Q →
      (∀ s' ∈ S, s' ∉ Q → orderOf s' < orderOf s → ∀ a' ∈ Q, ∀ g' : X, g'⁻¹ * a' * g' ≠ s') →
    ∀ a ∈ Q, ∀ g : X, g⁻¹ * a * g = s → g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) →
      s ∈ normalizer (Q : Set X) → s * s ∈ Q →
    ∀ hsN : s ∈ normalizer (M : Set X), ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 → ρ ⟨s, hsN⟩ ≠ 1 →
      5 ≤ (ρ ⟨s, hsN⟩).support.card → False

theorem signalizerNineConjugateInput_of_fusionCount (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hFC : SignalizerNineFusionCountInput) : SignalizerNineConjugateInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ Q S hQK hQ2 hQcard htQ hQS hSH
    hS2 hScard s hsS hsQ hmin a ha g hgs hgH hsNQ hs2Q hsN hρs2 hρs1
  by_cases h4 : (ρ ⟨s, hsN⟩).support.card ≤ 4
  · exact S₀.false_of_support_le_four h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup θ hρ
      (hQK.trans inf_le_left) (hQK.trans inf_le_right) hQ2 htQ (hSH hsS) hsNQ ha hgs hρs1 h4
  · exact hFC X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ Q S hQK hQ2 hQcard htQ hQS hSH
      hS2 hScard s hsS hsQ hmin a ha g hgs hgH hsNQ hs2Q hsN hρs2 hρs1 (by omega)

end CFSG.ComponentClassification.SolMax
