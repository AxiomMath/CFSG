module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def FiOrders : Prop :=
  Nat.card (Carrier .Fi22) < Nat.card (Carrier .Fi23) ∧
    Nat.card (Carrier .Fi23) < Nat.card (Carrier .Fi24Prime)

theorem noBiggerFi_fi24Prime_of_orders (ho : FiOrders) (H : Type) [Group H] :
    NoBiggerFi H .Fi24Prime := by
  intro L₁ s₁ _ hs₁ _
  have hs' : s₁ = .Fi22 ∨ s₁ = .Fi23 ∨ s₁ = .Fi24Prime := by simpa [fiTypes] using hs₁
  rcases hs' with rfl | rfl | rfl
  · exact (ho.1.trans ho.2).le
  · exact ho.2.le
  · exact le_rfl

@[expose] def FiNoUp (Up : List TauCeti.SporadicName) (H : Type) [Group H] : Prop :=
  ∀ Q : Subgroup H, InL Q → ∀ s'' ∈ Up, ¬ IsSporadic (↥Q ⧸ center ↥Q) s''

@[expose] def FiHyp31 (IsK : GroupClass) (S A Up : List TauCeti.SporadicName) : Prop :=
  Sol78Lit → Hyp31Row IsK (IsLS S) → ∀ (H : Type) [Group H] [Finite H],
    BelowSec (Sol78PredS A) H → ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → FiNoUp Up H → ¬ IsSporadic ↥N .Fi22 →
        ¬ IsSporadic ↥N .Fi23 → ¬ IsSporadic ↥N .Fi24Prime → ∀ L : Subgroup H, SolStd L →
          (∃ s ∈ S, OddCover s L) → Hyp31Glob H N IsK (IsLS S) ∧ Hyp31FourA H N IsK

@[expose] def FiVariantThree : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ¬ IsSporadic ↥N .Fi22 →
        ¬ IsSporadic ↥N .Fi23 → ¬ IsSporadic ↥N .Fi24Prime → NoBiggerFi H .Fi24Prime →
          (∃ L₀ : Subgroup H, SolStd L₀ ∧ OddCover .Fi24Prime L₀) →
            (∃ P : Subgroup H, InL P ∧ IsSporadic (↥P ⧸ center ↥P) .Fi23) →
              (¬ ∃ L₁ : Subgroup H, SolStd L₁ ∧ OddCover .Fi23 L₁) →
                ∃ (s' : TauCeti.SporadicName) (L' : Subgroup H), s' ∈ fiTypes ∧ OddCover s' L' ∧
                  FiOut H N L' s'

@[expose] def FiCoexist : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ¬ IsSporadic ↥N .Fi22 →
        ¬ IsSporadic ↥N .Fi23 → ¬ IsSporadic ↥N .Fi24Prime → NoBiggerFi H .Fi24Prime →
          (∃ L₀ : Subgroup H, SolStd L₀ ∧ OddCover .Fi24Prime L₀) →
            (∃ L₁ : Subgroup H, SolStd L₁ ∧ OddCover .Fi23 L₁) →
              ∃ (s' : TauCeti.SporadicName) (L' : Subgroup H), s' ∈ fiTypes ∧ OddCover s' L' ∧
                FiOut H N L' s'

end CFSG.EvenSporadicStandard.Induction.Fi
