module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThree

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley

@[expose] def F4ThreeInnerNonsplitLarge :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → Nat.card K ≠ 2 → Nat.card K ≠ 4 →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.F4 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.F4 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.F4 K)), innerAut (adjointGroup Tag.F4 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.F4 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def E6ThreeInnerNonsplitLarge :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ℓ ^ f ≠ 2 → ℓ ^ f ≠ 4 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.E6 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E6 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def E6ThreeDiagonalNonsplitLarge :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → 3 ∣ ℓ ^ f - 1 → ℓ ^ f ≠ 4 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ e6Inndiag K → ¬ D ≤ innerAut (adjointGroup Tag.E6 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E6 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def E7ThreeInnerNonsplitLarge :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ℓ ^ f ≠ 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E7 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.E7 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E7 K)), innerAut (adjointGroup Tag.E7 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E7 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def E8ThreeInnerNonsplitLarge :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ℓ ^ f ≠ 2 → ℓ ^ f ≠ 4 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E8 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.E8 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E8 K)), innerAut (adjointGroup Tag.E8 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E8 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def TwistedE6ThreeDiagonalLarge :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ (2 * f) →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ D : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 D →
      Nat.card D = 3 ^ 3 → D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ →
      ¬ D ≤ innerAut (twistedE6RootGroup K σ) →
      ∀ H : Subgroup (MulAut (twistedE6RootGroup K σ)),
        innerAut (twistedE6RootGroup K σ) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (twistedE6RootGroup K σ))) →
          localDeltaIn 3 H D = ⊥

@[expose] def TwistedE6ThreeInnerLarge : Prop :=
  CrossCharInnerAt .twistedE6 fun idx p =>
    p = 3 ∧ ∃ q : TauCeti.PrimePower, idx.1 = .twistedE6 q ∧ q.card ≠ 2

section Splits


theorem f4ThreeInnerNonsplit_of_large (h : F4ThreeInnerNonsplitLarge)
    (hs : SmallQThreeOneBalance) : F4ThreeInnerNonsplit :=
  f4ThreeInnerNonsplit_of_smallQ h (smallQThree_of_oneBalance hs).1

theorem e6ThreeInnerNonsplit_of_large (h : E6ThreeInnerNonsplitLarge)
    (hs : SmallQThreeOneBalance) : E6ThreeInnerNonsplit :=
  e6ThreeInnerNonsplit_of_smallQ h (smallQThree_of_oneBalance hs).2.1

theorem e6ThreeDiagonalNonsplit_of_large (h : E6ThreeDiagonalNonsplitLarge)
    (hs : SmallQThreeOneBalance) : E6ThreeDiagonalNonsplit :=
  e6ThreeDiagonalNonsplit_of_smallQ h (smallQThree_of_oneBalance hs).2.2.1

theorem twistedE6ThreeDiagonal_of_large (h : TwistedE6ThreeDiagonalLarge)
    (hs : SmallQThreeOneBalance) : TwistedE6ThreeDiagonal :=
  twistedE6ThreeDiagonal_of_smallQ h (smallQThree_of_oneBalance hs).2.2.2.2.1

theorem e7ThreeInnerNonsplit_of_large (h : E7ThreeInnerNonsplitLarge)
    (hs : SmallQThreeOneBalance) : E7ThreeInnerNonsplit :=
  e7ThreeInnerNonsplit_of_smallQ h (smallQThree_of_oneBalance hs).2.2.2.2.2.1

theorem e8ThreeInnerNonsplit_of_large (h : E8ThreeInnerNonsplitLarge)
    (hs : SmallQThreeOneBalance) : E8ThreeInnerNonsplit :=
  e8ThreeInnerNonsplit_of_smallQ h (smallQThree_of_oneBalance hs).2.2.2.2.2.2

theorem crossCharInnerAt_twistedE6_three_of_large
    (h : TwistedE6ThreeInnerLarge)
    (hs : SmallQThreeOneBalance) : CrossCharInnerAt .twistedE6 fun _ p => p = 3 :=
  crossCharInnerAt_twistedE6_three_of_smallQ h (smallQThree_of_oneBalance hs).2.2.2.1

end Splits

end CFSG.HardMathSupport.Timmesfeld.CrossChar
