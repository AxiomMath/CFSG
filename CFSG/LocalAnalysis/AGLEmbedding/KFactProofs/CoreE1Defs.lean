module

public import CFSG.Open.GeneratedCore

public section

namespace CFSG.AGLEmbedding.CoreE1

open CFSG.Open Subgroup

variable (K : Type*) [Group K] [Finite K]

@[expose] def MovesCentre (T E : Subgroup K) : Prop :=
  ∃ z ∈ T, z ≠ 1 ∧ (∀ t ∈ T, t * z = z * t) ∧
    (∀ w ∈ T, (∀ t ∈ T, t * w = w * t) → w ∈ zpowers z) ∧
    ∃ h ∈ GLBCore 3 1 E, z * (h * z * h⁻¹) ≠ 1 ∧ Nat.Coprime 3 (orderOf (z * (h * z * h⁻¹)))

@[expose] def TransitiveOn (E : Subgroup K) : Prop :=
  ∀ u ∈ E, ∀ v ∈ E, u ≠ 1 → v ≠ 1 → ∃ n ∈ normalizer (E : Set K), n * u * n⁻¹ = v

@[expose] def Datum : Prop :=
  ∀ T : Sylow 3 K, Nat.card (T : Subgroup K) = 27 ∧
    (∃ x ∈ (T : Subgroup K), ∃ y ∈ (T : Subgroup K), x * y ≠ y * x) ∧
    ∀ E : Subgroup K, E ≤ T → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      MovesCentre K T E ∨ TransitiveOn K E

end CFSG.AGLEmbedding.CoreE1
