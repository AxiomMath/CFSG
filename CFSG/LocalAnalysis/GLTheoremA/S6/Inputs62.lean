module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def ChevClosureQAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ q : ℕ, q.Prime → ∀ (X K A : Subgroup G), CFSG.Open.IsKGroup ↥X →
    GLAPComponent p X K → IsChevSimple q (PSimple p K) → IsElemAbelian p A →
    A ≤ Subgroup.normalizer (K : Set G) →
    ∀ J : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J →
      IsChevSimple q (PSimple p J)

theorem chevClosureAt_of_chevClosureQAt {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : ChevClosureQAt G p) : ChevClosureAt G p :=
  fun hp hp2 X K A hX hK hKc hA hAK J hJ => h hp hp2 p hp X K A hX hK hKc hA hAK J hJ

@[expose] def I2019At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
    ∀ (B D K J : Subgroup G), GLAIsBmax p B → B ≤ Subgroup.normalizer (K : Set G) →
      CFSG.Open.IsQuasisimple (PQuot p K) → IsChevSimple q (PSimple p K) →
      B ⊓ centModSubgroup p K ≠ ⊥ → D ≤ B → B ⊓ centModSubgroup p K ≤ D →
      (B ⊓ centModSubgroup p K).relIndex D ≤ p → p ^ 2 * Nat.card D ≤ Nat.card B →
      GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set G)) J →
      B ≤ Subgroup.normalizer (J : Set G) → (∀ b ∈ B, CentMod p J b ↔ b ∈ D) →
      ∀ T : Subgroup G, T ≤ K → IsPGroup 2 T →
        J ≤ Subgroup.normalizer ((T ⊔ GLAPPrimeCoreOf p K : Subgroup G) : Set G) →
        ⁅T, J⁆ ≤ GLAPPrimeCoreOf p K

@[expose] def I183DiagAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (A D J : Subgroup G) (𝒞 : Set (Subgroup G)),
    IsElemAbelian p D → A ≤ D → (A.subgroupOf D).index = p →
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer (A : Set G)) →
    GLAPComponent p (Subgroup.centralizer (D : Set G)) J →
    (∀ C ∈ 𝒞, GLAPComponent p (Subgroup.centralizer (A : Set G)) C) →
    (⨆ C ∈ 𝒞, C) = ⨆ g ∈ GLAPLayer p (Subgroup.centralizer (A : Set G)), GLBConj g J →
    (∀ C ∈ 𝒞, ∀ e ∈ D, GLBConj e C ∈ 𝒞) →
    (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ D, GLBConj e C = C') →
    (∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂) →
    ∀ C ∈ 𝒞, C ≤ J ⊔ centModSubgroup p C

end CFSG.LocalAnalysis.GLTheoremA
