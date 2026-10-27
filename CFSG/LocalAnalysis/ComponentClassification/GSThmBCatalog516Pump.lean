module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.UnbalancedLayer

@[expose] def CF516PumpUpAt (Y : Type) [Group Y] (L : Subgroup Y) (β : Y) : Prop :=
  ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    ∀ K : Subgroup Y, K ≤ L ⊓ centralizer ({β} : Set Y) →
      IsPComponent 2 (K.subgroupOf (L ⊓ centralizer ({β} : Set Y))) →
      ((p ^ f % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = p ^ f ∧
          Nonempty (K ⧸ pPrimeCore 2 K ≃* StatedProj (StatedSL 4 F))) ∨
        (p ^ f % 4 = 1 ∧ ∃ (F : Type) (_ : Field F), UnitaryFieldData p f F ∧
          Nonempty (K ⧸ pPrimeCore 2 K ≃* StatedProj (StatedSU 4 (p ^ f) F)))) →
    ∀ t ∈ K, orderOf t = 2 →
    ∀ J : Subgroup Y, J ≤ L ⊓ centralizer ({t} : Set Y) →
      IsPComponent 2 (J.subgroupOf (L ⊓ centralizer ({t} : Set Y))) →
      Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p (2 * f) → β ∈ coreActionKernel J →
    ∀ JB : Subgroup Y, JB ≤ J ⊓ K → ⁅JB, JB⁆ = JB → J ≤ JB ⊔ oddCoreIn J →
    K = L

@[expose] def CF516PumpUpInv : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SectionRank.IsKGroupCat Y → ∀ L : Subgroup Y,
    IsComponent L → ∀ β : Y, (∃ n : ℕ, β ^ 2 ^ n = 1) → β ∈ normalizer (L : Set Y) →
    L ≤ centralizer ({β ^ 2} : Set Y) → CF516PumpUpAt Y L β

@[expose] def CF516PumpUp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SectionRank.IsKGroupCat Y → ∀ L : Subgroup Y,
    IsComponent L → ∀ β : Y, (∃ n : ℕ, β ^ 2 ^ n = 1) → β ∈ normalizer (L : Set Y) →
    CF516PumpUpAt Y L β

end CFSG.ComponentClassification.GSThmB
