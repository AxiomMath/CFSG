module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev Gx (x : G) : Subgroup G := centralizer ({x} : Set G)

abbrev Gxy (x y : G) : Subgroup G := centralizer ({x, y} : Set G)

abbrev Gxyz (x y w : G) : Subgroup G := centralizer ({x, y, w} : Set G)

theorem mem_Gx {x g : G} : g ∈ Gx x ↔ x * g = g * x :=
  Subgroup.mem_centralizer_singleton_iff.trans eq_comm

theorem mem_Gxy {x y g : G} : g ∈ Gxy x y ↔ g ∈ Gx x ∧ g ∈ Gx y := by
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, Set.mem_insert_iff,
    forall_eq_or_imp, forall_eq]

theorem Gxy_eq_inf (x y : G) : Gxy x y = Gx x ⊓ Gx y := by
  ext g
  simp only [mem_Gxy, Subgroup.mem_inf]

theorem mem_Gxyz {x y w g : G} : g ∈ Gxyz x y w ↔ g ∈ Gx x ∧ g ∈ Gx y ∧ g ∈ Gx w := by
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, Set.mem_insert_iff,
    forall_eq_or_imp, forall_eq]

theorem Gxyz_eq_inf (x y w : G) : Gxyz x y w = Gxy x y ⊓ Gx w := by
  ext g
  simp only [mem_Gxyz, mem_Gxy, Subgroup.mem_inf, and_assoc]

theorem self_mem_Gx (x : G) : x ∈ Gx x := mem_Gx.2 rfl

@[expose] def GxSelf (x : G) : ↥(Gx x) := ⟨x, self_mem_Gx x⟩

@[expose] def derivedOf (H : Subgroup G) : Subgroup G :=
  (_root_.commutator ↥H).map H.subtype

abbrev Qz (z : G) : Subgroup G := CFSG.Open.pCoreOf 2 (Gx z)

abbrev Gbar (z : G) : Type := ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z)

@[expose] def ConjIn (K : Subgroup G) (x y : G) : Prop := ∃ k ∈ K, k * x * k⁻¹ = y

structure IsConjOrbit (K : Subgroup G) (S : Set G) : Prop where
  conj_mem : ∀ k ∈ K, ∀ c ∈ S, k * c * k⁻¹ ∈ S
  nonempty : S.Nonempty
  transitive : ∀ c ∈ S, ∀ c' ∈ S, ∃ k ∈ K, k * c * k⁻¹ = c'

structure IsOrbitPartition {ι : Type} (K : Subgroup G) (S : Set G) (P : ι → Set G) : Prop where
  subset : ∀ i, P i ⊆ S
  cover : ∀ c ∈ S, ∃ i, c ∈ P i
  disjoint : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  orbit : ∀ i, IsConjOrbit K (P i)

@[expose] def StabCard {ι : Type} (K : Subgroup G) (P : ι → Set G) (n : ι → ℕ) : Prop :=
  ∀ i, ∀ c ∈ P i, Nat.card ↥(K ⊓ Gx c) = n i

@[expose] def orb2A (a x : G) : Set G := {b | IsConj a b ∧ IsConj a (x * b)}

@[expose] def orb2AB (a z x : G) : Set G := {w | IsConj z w ∧ IsConj a (x * w)}

@[expose] def orb2B (a z x : G) : Set G := {b | IsConj a b ∧ IsConj z (x * b)}

@[expose] def orb2BB (a z x : G) : Set G := {w | IsConj z w ∧ IsConj z (x * w)}

@[expose] def orb3A (a x : G) : Set G :=
  {c | IsConj a c ∧ orderOf (x * c) = 3 ∧ (orb2A a x ∩ orb2A a c).Nonempty}

@[expose] def orb4A (a z x : G) : Set G := {c | IsConj a c ∧ IsConj z ((x * c) ^ 2)}

@[expose] def orb4B (a x : G) : Set G := {c | IsConj a c ∧ IsConj a ((x * c) ^ 2)}

@[expose] def orb6A (a x : G) : Set G :=
  {c | IsConj a c ∧ orderOf (x * c) = 6 ∧ IsConj a ((x * c) ^ 3)}

@[expose] def oddSet (a x : G) : Set G :=
  {c | IsConj a c ∧ c ≠ x ∧ Odd (orderOf (x * c)) ∧ ∃ t, IsConj a t ∧ t ∈ Gxy x c}

@[expose] def orb5A (a x : G) : Set G :=
  {c | c ∈ oddSet a x ∧ orderOf (x * c) = 5 ∧
    ∀ t, IsConj a t → t ∈ Gxy x c → IsNonsplitDoubleCoverOfS5 ↥(Gxyz x t c)}

@[expose] def orb5E (a x : G) : Set G :=
  {c | c ∈ oddSet a x ∧ orderOf (x * c) = 5 ∧
    ∀ t, IsConj a t → t ∈ Gxy x c →
      Nonempty (↥(Gxyz x t c) ≃* Multiplicative (ZMod 2) × DihedralGroup 5)}

@[expose] def gammaSet (a z x : G) : Set G :=
  {x} ∪ orb2A a x ∪ orb2B a z x ∪ orb3A a x ∪ orb4A a z x ∪ orb4B a x ∪ orb5A a x ∪
    orb5E a x ∪ orb6A a x

@[expose] def IsConjOrbitStab (K : Subgroup G) (S : Set G) (n : ℕ) : Prop :=
  IsConjOrbit K S ∧ ∀ c ∈ S, Nat.card ↥(K ⊓ Gx c) = n

@[expose] def IsElemTwo (n : ℕ) (E : Subgroup G) : Prop :=
  CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ n

@[expose] def IsMinusExtraspecial (m : ℕ) (D : Subgroup G) : Prop :=
  CFSG.IsExtraspecial 2 ↥D ∧ Nat.card D = 2 ^ (1 + 2 * m) ∧
    ¬ ∃ E : Subgroup G, E ≤ D ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (m + 1)

abbrev barOf (w : G) (x : ↥(Gx w)) : Gbar w := QuotientGroup.mk x

@[expose] def centQtilde (w x : G) : Set G :=
  {q | q ∈ Qz w ∧ ⁅q, x⁆ ∈ Subgroup.zpowers w}

inductive OrbitKind
  | k2A | k2B | k3A | k4A | k4B | k5A | k5E | k6A
  deriving DecidableEq

@[expose] def orbitOf (a z x : G) : OrbitKind → Set G
  | .k2A => orb2A a x
  | .k2B => orb2B a z x
  | .k3A => orb3A a x
  | .k4A => orb4A a z x
  | .k4B => orb4B a x
  | .k5A => orb5A a x
  | .k5E => orb5E a x
  | .k6A => orb6A a x

end CFSG.EvenSporadicStandard.HNRecog.Section3
