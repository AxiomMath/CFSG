module

public import CFSG.CGT.Timmesfeld75.Sec5OutBar
public import CFSG.CGT.Timmesfeld75.Sec3Iso
public import CFSG.CGT.Timmesfeld75.Sec5One

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def IsUIdx (T T₁ : Subgroup G) (h : G) : Prop :=
  conjSubgroup h T ≠ T ∧ Nat.card (normIn (conjSubgroup h T) T) = Nat.card (normIn T T₁)

@[expose] def hSubU (T T₁ : Subgroup G) : Subgroup G :=
  T ⊔ ⨆ (h : G) (_ : IsUIdx T T₁ h), normIn (conjSubgroup h T) T

@[expose] def secR₁ (T T₁ : Subgroup G) : Subgroup G :=
  ⨆ (h : G) (_ : IsUIdx T T₁ h), conjSubgroup h (secA T T₁)

@[expose] def Sec4NoA : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    ∀ a ∈ normD T, a ∉ T ⊔ normIn T₁ T → ¬ ∀ l ∈ normIn T₁ T, ⁅a, l⁆ ∈ T

@[expose] def Sec48 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    IsWC (barSub T (normIn T₁ T))

@[expose] def Sec4Nine : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    4 < Nat.card T → ∀ c ∈ hSubU T T₁, (∀ t ∈ T, c * t = t * c) → ∀ x ∈ hSubU T T₁, ⁅c, x⁆ ∈ T

end CFSG.CGT.Timmesfeld75
