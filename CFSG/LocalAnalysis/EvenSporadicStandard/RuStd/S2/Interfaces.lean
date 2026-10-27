module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Facts

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

@[expose] def HasKlein {Y : Type*} [Group Y] (S : Set Y) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a

structure RuTwoBFacts (Y : Type) [Group Y] : Prop where
  elt5 : ∀ u : Y, orderOf u = 2 → Nat.card (centralizer ({u} : Set Y)) = 116480 →
    ∃ f ∈ derivedCentralizer u, orderOf f = 5
  centralInv : ∀ u : Y, orderOf u = 2 → Nat.card (centralizer ({u} : Set Y)) = 116480 →
    ∃ u' : Y, orderOf u' = 2 ∧ u' ≠ u ∧ ∀ x ∈ centralizer ({u} : Set Y), x * u' = u' * x

structure RuFiveFacts (Y : Type) [Group Y] : Prop where
  exp5 : ∀ g : Y, IsPGroup 5 (zpowers g) → g ^ 5 = 1
  typeAB : ∀ f : Y, orderOf f = 5 →
    (Nat.card (centralizer ({f} : Set Y)) = 300 ∧
      HasKlein ((centralizer ({f} : Set Y) : Subgroup Y) : Set Y)) ∨
    (Nat.card (centralizer ({f} : Set Y)) = 1000 ∧
      ¬ HasKlein ((centralizer ({f} : Set Y) : Subgroup Y) : Set Y))
  typeA : ∀ f : Y, orderOf f = 5 → Nat.card (centralizer ({f} : Set Y)) = 300 →
    ∃ D : Subgroup Y, Nonempty (↥D ≃* A5) ∧ D ≤ centralizer ({f} : Set Y) ∧
      centralizer ({f} : Set Y) = zpowers f ⊔ D ∧ Disjoint (zpowers f) D
  conjA : ∀ f g : Y, orderOf f = 5 → orderOf g = 5 →
    Nat.card (centralizer ({f} : Set Y)) = 300 → Nat.card (centralizer ({g} : Set Y)) = 300 →
    ∃ c : Y, ∃ k : ℕ, c * f * c⁻¹ = g ^ k
  typeB : ∀ f : Y, orderOf f = 5 → Nat.card (centralizer ({f} : Set Y)) = 1000 →
    ∃ φ : (↥(centralizer ({f} : Set Y)) ⧸ CFSG.pCore 5 ↥(centralizer ({f} : Set Y))) →* Q8,
      Function.Injective φ
  count : ∀ f : Y, orderOf f = 5 → Nat.card (centralizer ({f} : Set Y)) = 300 →
    ∀ F : Subgroup Y, F ≤ centralizer ({f} : Set Y) → Nat.card F = 25 →
      Nat.card {x : Y // x ∈ F ∧ x ≠ 1 ∧ Nat.card (centralizer ({x} : Set Y)) = 1000} ≤ 4

structure RuThreeFacts (Y : Type) [Group Y] : Prop where
  card : ∀ r : Y, orderOf r = 3 → Nat.card (centralizer ({r} : Set Y)) = 2160
  oddCore : ∀ r : Y, orderOf r = 3 → ∀ N : Subgroup Y, N ≤ centralizer ({r} : Set Y) →
    (∀ x ∈ centralizer ({r} : Set Y), ∀ n ∈ N, x * n * x⁻¹ ∈ N) → Odd (Nat.card N) →
    N ≤ zpowers r
  quot : ∀ r : Y, orderOf r = 3 →
    ∃ φ : ↥(centralizer ({r} : Set Y)) →* M10, Function.Surjective φ ∧
      φ.ker = (zpowers r).subgroupOf (centralizer ({r} : Set Y))
  inv2A : ∀ r : Y, orderOf r = 3 → ∃ v ∈ centralizer ({r} : Set Y), orderOf v = 2 ∧
    Nat.card (centralizer ({v} : Set Y)) = 245760

end CFSG.EvenSporadicStandard.RuStd.S2
