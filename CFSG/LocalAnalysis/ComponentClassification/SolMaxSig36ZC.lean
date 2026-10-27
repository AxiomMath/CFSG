module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36E

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerCaseOneConjugateInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → 13 ≤ n → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M →
      ∀ hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X),
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)), IsPermAction θ ρ →
    ∀ Q : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ →
        normalizer (T : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
    ∀ (a g : X), a ∈ Q → g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) →
      ∀ hs : g⁻¹ * a * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g⁻¹ * a * g ∈ normalizer (Q : Set X) →
      ρ ⟨g⁻¹ * a * g, hHN hs⟩ * ρ ⟨g⁻¹ * a * g, hHN hs⟩ = 1 → ρ ⟨g⁻¹ * a * g, hHN hs⟩ ≠ 1 →
    ∀ (x : X) (hx : x ∈ M), x ∈ oddGen (centralizer ({g⁻¹ * a * g} : Set X)) → x * x = 1 →
      (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
    ∀ hx' : g * x * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card = 4 ∧
        centralizer ({g * x * g⁻¹} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)

@[expose] def SignalizerCaseOneStrongClosureElevenInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)) (E : Subgroup X) (D : Finset (Fin 11)),
    Sig36 X t J 11 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      ∀ a ∈ Q, ∀ g : X, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ Q

variable {X : Type} [Group X]

end CFSG.ComponentClassification.SolMax
