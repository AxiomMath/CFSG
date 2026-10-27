module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup

@[expose] def LayerPairFull : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Open.evenRank H ≤ 2 → CFSG.SectionRank.IsKGroupCat H →
    ∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ ≠ L₂ →
      Nonempty (↥L₁ ≃* ↥L₂) → ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥L₁) →
        r = 3 ∧ CFSG.Quasithin.IsSU3 8 ↥L₁ ∧ CFSG.Open.pRank 3 (L₁ ⊔ L₂) = 3

@[expose] def LayerPairList (S : Type) [Group S] : Prop :=
  CFSG.Quasithin.IsAlt 6 S ∨ CFSG.Quasithin.IsAlt 7 S ∨
    CFSG.Quasithin.IsSporadic .M22 S ∨
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧
      ((CFSG.Quasithin.IsPSL 3 p f S ∧ 3 ∣ p ^ f - 1) ∨
        (CFSG.Quasithin.IsPSU 3 p f S ∧ 3 ∣ p ^ f + 1))

@[expose] def LayerPairFact : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Open.evenRank H ≤ 2 → CFSG.SectionRank.IsKGroupCat H →
    ∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ ≠ L₂ →
      Nonempty (↥L₁ ≃* ↥L₂) → LayerPairList (↥L₁ ⧸ center ↥L₁) → 3 ∣ Nat.card (center ↥L₁) →
        CFSG.Quasithin.IsSU3 8 ↥L₁ ∧ CFSG.Open.pRank 3 (L₁ ⊔ L₂) = 3

@[expose] def LayerPairJ3 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Open.evenRank H ≤ 2 → CFSG.SectionRank.IsKGroupCat H →
    ∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ ≠ L₂ →
      Nonempty (↥L₁ ≃* ↥L₂) → CFSG.Quasithin.IsSporadic .J3 (↥L₁ ⧸ center ↥L₁) →
        ¬ 3 ∣ Nat.card (center ↥L₁)

end CFSG.SectionRank.QTK.CentreFact
