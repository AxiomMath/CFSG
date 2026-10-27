module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup

@[expose] def HasSixOrbit {G : Type} [Group G] {D : Subgroup G}
    (φ : alternatingGroup (Fin 8) ≃* ↥D) (K : Subgroup G) : Prop :=
  ∃ i : Fin 8, Set.ncard {j : Fin 8 | ∃ g : alternatingGroup (Fin 8), (φ g : G) ∈ K ∧
    (g : Equiv.Perm (Fin 8)) i = j} = 6

@[expose] def Segev27 : Prop :=
  ∀ (H : Type) [Group H] (a b : H), IsShapeTwoTwoTimesA8 H →
    (center H : Set H) = {1, a, b, a * b} →
    ∀ (φ : alternatingGroup (Fin 8) ≃* ↥(commutator H)) (K : Fin 4 → Subgroup H),
      (∀ i : Fin 4, i.val < 2 → IsShapeZ2TimesSym 5 ↥(K i) ∧
        derivedOf (K i) = K i ⊓ commutator H ∧ IsShapeA5 ↥(derivedOf (K i)) ∧
        HasSixOrbit φ (derivedOf (K i))) →
      K 0 ⊓ center H = zpowers a → K 1 ⊓ center H = zpowers b →
      (∀ i : Fin 4, 2 ≤ i.val → IsShapeZ2TimesSym 6 ↥(K i)) →
      ∀ i j : Fin 4, i ≠ j → ∃ t ∈ K i ⊓ K j, orderOf t = 2

@[expose] def Segev28 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (t : H), orderOf t = 2 →
    (∀ S : Sylow 2 ↥(Gx t), (∀ x : ↥(Gx t),
        (x ∈ centerOf (S : Subgroup ↥(Gx t)) ∧ x ^ 2 = 1) ↔ x ∈ zpowers (GxSelf t)) ∧
      2 < Nat.card S) →
    Gx t = closure ((Gx t : Set H) ∩ {x | IsConj t x}) →
    (∀ N : Subgroup ↥(Gx t), N.Normal → N ≠ ⊥ → GxSelf t ∈ N) →
    IsSimpleGroup H

end CFSG.EvenSporadicStandard.HNRecog.Section3
