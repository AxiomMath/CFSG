module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Ext26

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank.G2Three.Sec2
open scoped commutatorElement

@[expose] def Y63ZE64 {G : Type} [Group G] (Z U : Subgroup G) : Prop :=
  Z ≤ U ∧ Nat.card ↥U = 2 ^ 7 ∧ (∀ x ∈ U, x ^ 2 ∈ Z) ∧ ⁅U, U⁆ ≤ Z

@[expose] def HSSylowFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q P M S : Subgroup G) (t : G),
    P ≤ Q → Nat.card ↥Q = 2 * Nat.card ↥P → IsHSType ↥P → t ∈ Q → t ∉ P → t ^ 2 = 1 →
    M ≤ P → P ≤ normalizer (M : Set G) → IsMulCommutative ↥M →
    Nonempty (↥M ≃* (Fin 3 → Multiplicative (ZMod 4))) →
    S ≤ P → Nat.card ↥S = 64 → S ⊔ M = P → omega1 M ≤ S →
    (∀ x ∈ S, t * x * t⁻¹ = x) → (∀ m ∈ M, t * m * t⁻¹ = m⁻¹) →
      Nat.card ↥(cen Q) = 2 ∧
      ∃ U : Subgroup G, U ≤ Q ∧ Y63ZE64 (cen Q) U ∧
        (∀ U' : Subgroup G, U' ≤ Q → Y63ZE64 (cen Q) U' → U' = U) ∧
        ∀ x ∈ P, orderOf x = 2 → 2 ^ 7 ≤ Nat.card ↥(centEl Q x) →
          x ∉ ⁅centEl Q x, centEl Q x⁆ → x ∈ U ∧ cen Q ≤ ⁅centEl Q x, centEl Q x⁆

end CFSG.OddStandard.HigherRank.YamadaG23
