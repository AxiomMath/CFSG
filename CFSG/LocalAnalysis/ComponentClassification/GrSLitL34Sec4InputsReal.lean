
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsRealBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEights

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def L34BFixExponentFact : Prop :=
  ∀ (E : Type) [Group E] (q : E →* Equiv.Perm (Fin 42)) (l : Cover →* E), IsQSetting q l →
    IsCyclic ↥q.ker → Nat.card ↥q.ker = 4 →
    ∀ y ∈ R, (∀ t ∈ T0, y * t * y⁻¹ ∈ T0) → ∀ β : E ≃* E, (∀ e, q (β e) = y * q e * y⁻¹) →
      (∀ b ∈ l34BHat q, β b = b) → y ^ 4 = 1

@[expose] def L34BFixOuterSquareFact : Prop :=
  ∀ (E : Type) [Group E] (q : E →* Equiv.Perm (Fin 42)) (l : Cover →* E), IsQSetting q l →
    IsCyclic ↥q.ker → Nat.card ↥q.ker = 4 →
    ∀ y ∈ R, y ∉ S → (∀ t ∈ T0, y * t * y⁻¹ ∈ T0) → ∀ β : E ≃* E,
      (∀ e, q (β e) = y * q e * y⁻¹) → (∀ b ∈ l34BHat q, β b = b) →
      ∀ w, q w ∈ T0 → β w = w → (∀ e, β (β e) = w * e * w⁻¹) →
        (∃ v ∈ l34AHat q, v * β v * w = 1) ∨
          (∃ v ∈ l34AHat q, (v * β v * w) ^ 2 ∈ q.ker ∧ (v * β v * w) ^ 2 ≠ 1) ∨
          ∀ v ∈ l34AHat q, v * β v * w ∈ q.ker ∧ (v * β v * w) ^ 2 = 1 ∧ v * β v * w ≠ 1

@[expose] def L34OuterCentralizerCosetFact : Prop :=
  ∀ (E : Type) [Group E] (q : E →* Equiv.Perm (Fin 42)) (l : Cover →* E), IsQSetting q l →
    IsCyclic ↥q.ker → Nat.card ↥q.ker = 4 →
    ∀ ρ : Equiv.Perm (Fin 42), (ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) → ∀ β : E ≃* E,
      (∀ e, q (β e) = ρ * q e * ρ⁻¹) →
      ∀ r ∈ R, (∀ t ∈ T0, r * t * r⁻¹ ∈ T0) → r * ρ = ρ * r → r * r = 1 →
        (∀ e, q e ∈ T0 → β e = e → r * q e = q e * r) → r ∈ S ∨ r * ρ ∈ S

@[expose] def L34OuterFixedInvolutionFact : Prop :=
  ∀ (E : Type) [Group E] (q : E →* Equiv.Perm (Fin 42)) (l : Cover →* E), IsQSetting q l →
    IsCyclic ↥q.ker → Nat.card ↥q.ker = 4 →
    ∀ ρ : Equiv.Perm (Fin 42), (ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) → ∀ β : E ≃* E,
      (∀ e, q (β e) = ρ * q e * ρ⁻¹) →
      ∀ Y : Subgroup (Equiv.Perm (Fin 42)), IsPGroup 2 ↥Y → Y ≤ R →
        (∀ r ∈ Y, ∀ t ∈ T0, r * t * r⁻¹ ∈ T0) → (∀ r ∈ Y, r * ρ = ρ * r) → ρ ∈ Y →
        (∀ e, q e ∈ T0 → β e = e → q e ∈ Y) →
        ∃ w, q w ∈ T0 ∧ w * w = 1 ∧ q w ≠ 1 ∧
          ∀ r ∈ Y, ∀ β' : E ≃* E, (∀ e, q (β' e) = r * q e * r⁻¹) → β' w = w

@[expose] def L34OuterCommutatorFact : Prop :=
  ∀ (E : Type) [Group E] (q : E →* Equiv.Perm (Fin 42)) (l : Cover →* E), IsQSetting q l →
    IsCyclic ↥q.ker → Nat.card ↥q.ker = 4 →
    ∀ ρ : Equiv.Perm (Fin 42), (ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) → ∀ β : E ≃* E,
      (∀ e, q (β e) = ρ * q e * ρ⁻¹) → (∀ z ∈ q.ker, β z = z⁻¹) →
      ∀ w, q w ∈ T0 → w * w = 1 → β w = w → ∃ v, q v ∈ T0 ∧ (β v)⁻¹ * v = w

end CFSG.ComponentClassification.GrSLit
