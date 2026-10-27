module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def Fi23Transposition {G : Type} [Group G] (L : Subgroup G) (u : G) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧
    Nat.card (L ⊓ centralizer ({u} : Set G) : Subgroup G) = 129123503308800

structure Fi23Local612 (G : Type) [Group G] (L : Subgroup G) : Prop where
  conj_elemAbelian : ∀ A A' : Subgroup G, A ≤ L → A' ≤ L → IsElemAbelian 2 A →
    IsElemAbelian 2 A' → Nat.card A = 2 ^ 11 → Nat.card A' = 2 ^ 11 →
      ∃ y ∈ L, A' = A.map (MulAut.conj y).toMonoidHom
  exists_transposition : ∃ u : G, Fi23Transposition L u
  frame : ∀ u : G, Fi23Transposition L u → ∃ W : Subgroup G, W ≤ L ∧ u ∈ W ∧
    IsElemAbelian 2 W ∧ Nat.card W = 2 ^ 11 ∧ centralizer (W : Set G) ⊓ L = W ∧
    (∃ _hN : (W.subgroupOf (normalizer (W : Set G) ⊓ L)).Normal,
      Nonempty ((normalizer (W : Set G) ⊓ L : Subgroup G) ⧸
        W.subgroupOf (normalizer (W : Set G) ⊓ L) ≃* Carrier .M23)) ∧
    Set.ncard {x : G | x ∈ W ∧ ∃ l ∈ L, x = l * u * l⁻¹} = 23 ∧
    ∀ p : G, p ∈ W → (∃ l ∈ L, p = l * u * l⁻¹) →
      ∃ n ∈ normalizer (W : Set G) ⊓ L, n * u * n⁻¹ = p

@[expose] def Fi23Lemma63 : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G), IsSporadic L .Fi23 → Fi23Local612 G L

end CFSG.EvenSporadicStandard.Solomon78
