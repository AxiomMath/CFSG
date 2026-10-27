module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

@[expose] def CF516PumpLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → SectionRank.IsKGroupCat S →
    ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    ((p ^ f % 4 = 3 ∧ Blueprint.LieModel (P ⧸ pPrimeCore 2 P) .PSL 4 p f) ∨
      (p ^ f % 4 = 1 ∧ Blueprint.LieModel (P ⧸ pPrimeCore 2 P) .PSU 4 p f)) →
    ∀ t ∈ P, orderOf t = 2 →
    ∀ J : Subgroup S, J ≤ centralizer ({t} : Set S) →
      IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set S))) →
      Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p (2 * f) →
      (∀ j ∈ J, σ j ∈ J) → (∀ j ∈ J, j⁻¹ * σ j ∈ oddCoreIn J) →
    ∀ JB : Subgroup S, JB ≤ J ⊓ P → ⁅JB, JB⁆ = JB → J ≤ JB ⊔ oddCoreIn J → False

end CFSG.ComponentClassification.GSThmB
