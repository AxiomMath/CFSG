module

public import CFSG.LocalAnalysis.ABGTheoremB.V3Defs

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure LemmaV31Input (σ : Setting G) (J : Subgroup G) : Prop where
  coprime : ∀ W ∈ σ.familyW J, ¬ σ.p ∣ Nat.card W
  comm : ∀ a ∈ σ.C ⊓ J, ∀ b ∈ σ.C ⊓ J, a * b * a⁻¹ * b⁻¹ ∈ pCoreIn σ.p σ.N
  covers : ∀ W ∈ σ.familyW J, ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
    ((W ⊔ σ.D : Subgroup G) : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G)

@[expose] def CommutatorInput (σ : Setting G) : Prop :=
  ⁅σ.N, σ.N⁆ ≤ σ.L₀

@[expose] def LemmaII42Input (σ : Setting G) (J : Subgroup G) : Prop :=
  ∀ W ∈ σ.familyW J, ∀ X : Subgroup G, X ≤ oddCoreIn σ.C → W ≤ X → ∀ y ∈ X,
    (∀ z ∈ ⁅X, X⁆, y * z * y⁻¹ * z⁻¹ ∈ σ.ON) → y ∈ σ.L

@[expose] def LemmaII46Input (σ : Setting G) (J : Subgroup G) : Prop :=
  ∀ W ∈ σ.familyW J, ∀ r : ℕ, r.Prime → r ∣ Nat.card W →
    ∀ W₀ : Subgroup G, W₀ ≤ oddCoreIn σ.C ⊓ σ.L → ¬ W₀ ≤ σ.ON →
    ∀ Y : Subgroup G, Y ≤ σ.N → IsPGroup r Y → ⁅Y, σ.T⁆ = Y → ¬ Y ≤ σ.ON →
      Even (Nat.card (W₀ ⊔ Y ⊔ σ.ON : Subgroup G))

@[expose] def LemmaII49Input (σ : Setting G) (J : Subgroup G) : Prop :=
  ∀ W ∈ σ.familyW J, ∀ Y : Subgroup G, Y ≤ σ.N → Odd (Nat.card Y) →
    σ.D ≤ Subgroup.normalizer (Y : Set G) → W ≤ Y → Y ≤ σ.C ⊔ σ.ON

@[expose] def QGroupSignalizerInput (σ : Setting G) : Prop :=
  ∀ H : Subgroup G, IsQGroup H → σ.D ≤ H →
    ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆ (H : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G) →
    ∀ U ∈ signalizers H σ.D σ.p, U ≤ oddCoreIn H ⊔ (H ⊓ σ.C)

@[expose] def DGroupSignalizerInput (σ : Setting G) : Prop :=
  σ.height = 1 → ∀ H : Subgroup G, σ.D ≤ H → IsDGroup H →
    ∀ Z : Subgroup G, Z ≤ H → Odd (Nat.card Z) → σ.D ≤ Subgroup.normalizer (Z : Set G) →
      Z ≤ oddCoreIn H ⊔ oddCoreIn (H ⊓ σ.N)

end CFSG.ABGTheoremB.V4
