module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

@[expose] def tTH {H : Type} [Group H] (a z z₁ y : H) : Prop :=
  IsConj y a ∨ IsConj y (a * z) ∨ IsConj y z₁

@[expose] def WsubH {H : Type} [Group H] (a z z₁ x : H) : Subgroup H :=
  Subgroup.closure {y : H | y ∈ centralizer ({x} : Set H) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ tTH a z z₁ y}

structure HaradaFacts3 (H : Type) [Group H] (E : Subgroup H) (a z b z₁ : H)
    (S T T' W0 : Subgroup H) (ι : Elem2 6 →* H) : Prop
    extends HaradaFacts H E a z b z₁ S T T' W0 ι where
  three_conj : ∀ x y : H, orderOf x = 3 → orderOf y = 3 → IsConj x y
  card_C3 : ∀ x : H, orderOf x = 3 → Nat.card (centralizer ({x} : Set H)) = 1440
  odd_normal : ∀ x : H, orderOf x = 3 → ∀ N : Subgroup H, N ≤ centralizer ({x} : Set H) →
    (∀ c ∈ centralizer ({x} : Set H), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card N) →
    N ≤ zpowers x
  card_tT : ∀ x : H, orderOf x = 3 →
    Set.ncard {y : H | y ∈ centralizer ({x} : Set H) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ tTH a z z₁ y} = 46
  perfect60 : ∀ x : H, orderOf x = 3 → ∃ M : Subgroup H, M ≤ centralizer ({x} : Set H) ∧
    ⁅M, M⁆ = M ∧ Nat.card M = 60 ∧ M ⊓ zpowers x = ⊥
  W_comm : ∀ x : H, orderOf x = 3 → ∃ s : H, s ∈ centralizer ({x} : Set H) ∧ s ^ 2 = 1 ∧
    s ≠ 1 ∧ tTH a z z₁ s ∧ s ∈ ⁅WsubH a z z₁ x, WsubH a z z₁ x⁆

@[expose] def HaradaInterface3 : Prop :=
  ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∃ (a z b z₁ : H) (S T T' W0 : Subgroup H) (ι : Elem2 6 →* H),
      HaradaFacts3 H E a z b z₁ S T T' W0 ι

end CFSG.EvenSporadicStandard.HNRecog
