module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup MulAction

structure OrbitData {V : Type} [CommGroup V] (M : Subgroup (MulAut V)) (t : V)
    (O : Fin 5 → Set V) : Prop where
  ne_one : t ≠ 1
  isOrbit : ∀ i, ∃ x : V, O i = orbit M x
  ncard : ∀ i, (O i).ncard = ![22, 22, 231, 231, 1540] i
  disjoint : ∀ i j, i ≠ j → Disjoint (O i) (O j)
  not_mem_one : ∀ i, (1 : V) ∉ O i
  not_mem_t : ∀ i, t ∉ O i
  cover : ∀ v : V, v ≠ 1 → v = t ∨ ∃ i, v ∈ O i
  fix : ∀ m ∈ M, m t = t
  swap : O 1 = (fun u => t * u) '' O 0
  prod : ∀ u ∈ O 0, ∀ u' ∈ O 0, u ≠ u' → u * u' ∈ O 2
  gen : Subgroup.closure (insert t (O 0)) = ⊤

@[expose] def GLDvdStmt : Prop :=
  ∀ {V : Type} [CommGroup V] [Finite V], Nat.card V = 2 ^ 11 → (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V),
      Nat.card X ∣ 2 ^ 55 * 3 ^ 6 * 5 ^ 2 * 7 ^ 3 * 11 * 17 * 23 * 31 ^ 2 * 73 * 89 * 127

@[expose] def NoCard2047Stmt : Prop :=
  ∀ {V : Type} [CommGroup V] [Finite V], Nat.card V = 2 ^ 11 → (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), Nat.card X ≠ 23 * 89 * 887040

@[expose] def IdxDvd11Stmt : Prop :=
  ∀ {V : Type} [CommGroup V] [Finite V], Nat.card V = 2 ^ 11 → (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), Nat.card X = 244823040 →
      ∀ K : Subgroup X, K.Normal → 23 ∣ Nat.card K → K.index ∣ 11

@[expose] def Orbit23Stmt : Prop :=
  ∀ {V : Type} [CommGroup V] [Finite V], Nat.card V = 2 ^ 11 → (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), Nat.card X = 244823040 →
      ∀ y : V, y ≠ 1 → 23 ∣ Nat.card (orbit X y)

@[expose] def SimpleOfShapeStmt : Prop :=
  ∀ {V : Type} [CommGroup V] [Finite V], Nat.card V = 2 ^ 11 → (∀ v : V, v ^ 2 = 1) →
    ∀ (X M : Subgroup (MulAut V)) (t : V) (O : Fin 5 → Set V), M ≤ X → OrbitData M t O →
      Nat.card M = 443520 → Nat.card ↥(X ⊓ stabilizer (MulAut V) t) = 887040 →
      (∃ ν ∈ X, ν t = t ∧ (fun v => ν v) '' O 0 = O 1) → Nat.card X = 244823040 →
      (orbit X t).ncard = 276 → IsSimpleGroup X

@[expose] def CocodeMainStmt : Prop :=
  ∀ {V : Type} [CommGroup V] [Finite V], Nat.card V = 2 ^ 11 → (∀ v : V, v ^ 2 = 1) →
    ∀ (X M : Subgroup (MulAut V)) (t : V) (O : Fin 5 → Set V), M ≤ X → OrbitData M t O →
      Nat.card M = 443520 → Nat.card ↥(X ⊓ stabilizer (MulAut V) t) = 887040 →
      (∃ x ∈ X, x t ≠ t) → (∃ ν ∈ X, ν t = t ∧ (fun v => ν v) '' O 0 = O 1) →
        IsSimpleGroup X ∧ Nat.card X = 244823040 ∧ (orbit X t).ncard = 276 ∧
          ∃ y : V, y ≠ 1 ∧ y ∉ orbit X t ∧ (orbit X y).ncard = 1771 ∧
            ∀ w : V, w ≠ 1 → w ∉ orbit X t → w ∈ orbit X y

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
