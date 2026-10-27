module

public import CFSG.Holt.General.Defs
public import CFSG.CGT.Timmesfeld75.PaperSteps

public section

namespace CFSG.CGT.M24S

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Holt.General

variable {G : Type} [Group G]

structure Hyp (T H : Subgroup G) : Prop where
  le : T ≤ H
  wc : IsWC T
  nat : NaturalSL T H 4 1
  odd : Odd H.index

structure LocalFacts (T H : Subgroup G) : Prop where
  card_T : Nat.card T = 16
  card_H : Nat.card H = 322560
  card_sylow : ∀ S : Sylow 2 G, Nat.card S = 2 ^ 10
  le_normalizer : H ≤ Subgroup.normalizer (T : Set G)
  inf_centralizer : H ⊓ Subgroup.centralizer (T : Set G) = T
  normalizer_eq : Subgroup.normalizer (T : Set G) = H ⊔ Subgroup.centralizer (T : Set G)
  transitive : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ H, h * x * h⁻¹ = y
  isTI : IsTI T
  centralizer_le : ∀ x ∈ T, x ≠ 1 →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (T : Set G)
  centralizer_T_eq : Subgroup.centralizer (T : Set G) =
    T ⊔ oddCoreOf (Subgroup.centralizer (T : Set G))
  centralizer_eq : ∀ x ∈ T, x ≠ 1 → Subgroup.centralizer ({x} : Set G) =
    (H ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ oddCoreOf (Subgroup.centralizer (T : Set G))
  oddCore_eq : ∀ x ∈ T, x ≠ 1 → oddCoreOf (Subgroup.centralizer ({x} : Set G)) =
    oddCoreOf (Subgroup.centralizer (T : Set G))
  sylow : ∃ S : Sylow 2 G, T ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ H ∧ ∃ z₀ ∈ T, z₀ ≠ 1 ∧
    ∀ x ∈ (S : Subgroup G), ((∀ y ∈ (S : Subgroup G), x * y = y * x) ↔ (x = 1 ∨ x = z₀))

@[expose] def IsExtraspecialAt (E : Subgroup G) (z : G) : Prop :=
  IsPGroup 2 E ∧ z ∈ E ∧ orderOf z = 2 ∧
    (∀ x ∈ E, ((∀ y ∈ E, x * y = y * x) ↔ (x = 1 ∨ x = z))) ∧
    (∀ x ∈ E, x ^ 2 = 1 ∨ x ^ 2 = z) ∧
    (∀ x ∈ E, ∀ y ∈ E, x⁻¹ * y⁻¹ * x * y = 1 ∨ x⁻¹ * y⁻¹ * x * y = z)

end CFSG.CGT.M24S
