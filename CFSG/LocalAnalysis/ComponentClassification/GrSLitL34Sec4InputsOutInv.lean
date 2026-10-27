module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34OuterInvolutionCenterInvStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 →
    IsCyclic ↥(S ⊓ coreActionKernel J) →
    (∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) →
    (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
    ∀ b ∈ S, b * b = 1 → b ∉ withKernel J → (∀ z ∈ S ⊓ zStarIn J, b * z * b⁻¹ = z⁻¹) →
      (∀ y ∈ S ⊓ centralizer ({b} : Set G), (∀ t ∈ S ⊓ centralizer ({b} : Set G),
          y * t = t * y) → y * y = 1 → y ∈ J ∨ b * y ∈ J) ∧
      (∃ z ∈ J ⊓ (S ⊓ centralizer ({b} : Set G)),
          (∀ t ∈ S ⊓ centralizer ({b} : Set G), z * t = t * z) ∧ z * z = 1 ∧ z ≠ 1 ∧ z ≠ a) ∧
      ∀ z ∈ J ⊓ (S ⊓ centralizer ({b} : Set G)),
        (∀ t ∈ S ⊓ centralizer ({b} : Set G), z * t = t * z) → z * z = 1 →
          ∃ s ∈ S, s⁻¹ * b * s = b * z

end CFSG.ComponentClassification.GrSLit
