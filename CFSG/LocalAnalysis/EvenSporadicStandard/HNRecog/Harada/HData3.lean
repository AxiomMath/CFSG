module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

@[expose] def tTG {G : Type} [Group G] (t z z₁ y : G) : Prop :=
  (∃ h ∈ centralizer ({t} : Set G), h * y * h⁻¹ = t) ∨
  (∃ h ∈ centralizer ({t} : Set G), h * y * h⁻¹ = t * z) ∨
  (∃ h ∈ centralizer ({t} : Set G), h * y * h⁻¹ = z₁)

@[expose] def WsubG {G : Type} [Group G] (t z z₁ x : G) : Subgroup G :=
  Subgroup.closure {y : G | y ∈ centralizer ({t} : Set G) ∧ y ∈ centralizer ({x} : Set G) ∧
    y ^ 2 = 1 ∧ y ≠ 1 ∧ tTG t z z₁ y}

structure HData3 (G : Type) [Group G] (t z z₁ : G) : Prop where
  three_conj : ∀ x ∈ centralizer ({t} : Set G), ∀ y ∈ centralizer ({t} : Set G),
    orderOf x = 3 → orderOf y = 3 → ∃ h ∈ centralizer ({t} : Set G), h * x * h⁻¹ = y
  card_C3 : ∀ x ∈ centralizer ({t} : Set G), orderOf x = 3 →
    Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G)) = 1440
  odd_normal : ∀ x ∈ centralizer ({t} : Set G), orderOf x = 3 → ∀ N : Subgroup G,
    N ≤ centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) →
    (∀ c ∈ centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G), ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
    Odd (Nat.card N) → N ≤ zpowers x
  card_tT : ∀ x ∈ centralizer ({t} : Set G), orderOf x = 3 →
    Set.ncard {y : G | y ∈ centralizer ({t} : Set G) ∧ y ∈ centralizer ({x} : Set G) ∧
      y ^ 2 = 1 ∧ y ≠ 1 ∧ tTG t z z₁ y} = 46
  perfect60 : ∀ x ∈ centralizer ({t} : Set G), orderOf x = 3 → ∃ M : Subgroup G,
    M ≤ centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) ∧ ⁅M, M⁆ = M ∧ Nat.card M = 60 ∧
      M ⊓ zpowers x = ⊥
  W_comm : ∀ x ∈ centralizer ({t} : Set G), orderOf x = 3 → ∃ s : G,
    s ∈ centralizer ({t} : Set G) ∧ s ∈ centralizer ({x} : Set G) ∧ s ^ 2 = 1 ∧ s ≠ 1 ∧
    tTG t z z₁ s ∧ s ∈ ⁅WsubG t z z₁ x, WsubG t z z₁ x⁆

end CFSG.EvenSporadicStandard.HNRecog.Harada
