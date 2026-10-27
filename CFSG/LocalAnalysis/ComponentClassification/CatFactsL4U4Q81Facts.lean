module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

structure L4U4ThreeInvolutionFacts : Prop where
  cent : ∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G), IsQuasisimple ↥Q →
    (Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSU 4 3 1) →
    Nat.card ↥(center ↥Q) ∣ 2 → ∀ w ∈ Q, orderOf w = 2 →
    ∀ X₁ X₂ : Subgroup G, X₁ ≠ X₂ → X₁ ≤ Q ⊓ centralizer {w} → X₂ ≤ Q ⊓ centralizer {w} →
      (X₁.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal →
      (X₂.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal →
      X₁ ≤ centralizer (X₂ : Set G) → X₁ ⊓ X₂ = zpowers w →
      IsSLTwoOver 3 ↥X₁ → IsSLTwoOver 3 ↥X₂ →
      X₁ ⊔ X₂ = closure {g : G | g ∈ Q ⊓ centralizer {w} ∧ Odd (orderOf g)}
  pgl : ∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G), IsQuasisimple ↥Q →
    (Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSU 4 3 1) →
    Nat.card ↥(center ↥Q) ∣ 2 →
    ∀ (t : G) (D : Subgroup G), t ∈ normalizer (Q : Set G) → orderOf t = 2 →
      Blueprint.LieModel ↥(GSThmB.layerIn (Q ⊓ centralizer {t})) .PSL 2 3 2 →
      D ≤ normalizer (Q : Set G) → D ≤ centralizer {t} → Nonempty (↥D ≃* DihedralGroup 8) →
      Nat.card ↥(D ⊓ GSThmB.layerIn (Q ⊓ centralizer {t})) = 8 →
      ∀ x ∈ D, x ∉ GSThmB.layerIn (Q ⊓ centralizer {t}) → orderOf x = 2 →
        ∃ J : Subgroup G, J ≤ Q ⊓ centralizer {x} ∧
          IsPComponent 2 (J.subgroupOf (Q ⊓ centralizer {x})) ∧ IsOfType (HarrisF 3) ↥J

end CFSG.ComponentClassification.HarrisLit
