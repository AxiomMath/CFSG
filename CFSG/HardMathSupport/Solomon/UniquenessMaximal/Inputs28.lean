module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Vocab
public import CFSG.Open.StatedDefs
public import CFSG.Open.GLADefs
public import CFSG.HardMathSupport.Solomon.Coordinator.Defs
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def IsElemAbelianTwo (V : Type) [CommGroup V] : Prop := ∀ v : V, v * v = 1

@[expose] def IsTransvection {V : Type} [CommGroup V] (τ : MulAut V) : Prop :=
  τ ≠ 1 ∧ Nat.card (Subgroup.closure (Set.range fun v : V => τ v * v⁻¹)) = 2

@[expose] def IsMcLaughlinGroup (W : Type) [Group W] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ Nonempty (W ≃* ↥(StatedSL n (ZMod 2)))) ∨
  (∃ n : ℕ, 2 ≤ n ∧ Nonempty (W ≃* ↥(StatedSp n (ZMod 2)))) ∨
  (∃ n : ℕ, 2 ≤ n ∧ Nonempty (W ≃* ↥(GLAOrthGroup (GLAQPlus (ZMod 2) n)))) ∨
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty (W ≃* ↥(GLAOrthGroup (GLAQMinus n (1 : ZMod 2) 1)))) ∨
  (∃ n : ℕ, 5 ≤ n ∧ Nonempty (W ≃* Equiv.Perm (Fin n)))

@[expose] def IsMcLaughlinDecomposition {V : Type} [CommGroup V] (X : Subgroup (MulAut V))
    (τ : MulAut V) (r : ℕ) (W : Fin (r + 1) → Subgroup (MulAut V)) : Prop :=
  (⨆ i, W i) = Subgroup.closure {τ' | ∃ g ∈ X, τ' = g⁻¹ * τ * g} ∧
    (∀ i, W i ≤ X) ∧
    (∀ i j, i ≠ j → W i ≤ Subgroup.centralizer (W j : Set (MulAut V))) ∧
    (∀ i, W i ⊓ (⨆ j : {j // j ≠ i}, W j) = ⊥) ∧
    (∀ i, ∃ g ∈ X, GLBConj g (W 0) = W i) ∧ (∀ g ∈ X, ∀ i, ∃ j, GLBConj g (W i) = W j) ∧
    τ ∈ W 0 ∧ (∀ i, IsMcLaughlinGroup ↥(W i))

@[expose] def Input28_5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], IsElemAbelianTwo V → ∀ X : Subgroup (MulAut V),
    pCoreOf 2 X = ⊥ → ∀ τ ∈ X, IsTransvection τ →
      ∃ (r : ℕ) (W : Fin (r + 1) → Subgroup (MulAut V)), IsMcLaughlinDecomposition X τ r W

@[expose] def Input28_14 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], IsElemAbelianTwo V → ∀ X : Subgroup (MulAut V),
    pCoreOf 2 X = ⊥ → ∀ τ ∈ X, IsTransvection τ →
      ∀ (r : ℕ) (W : Fin (r + 1) → Subgroup (MulAut V)), IsMcLaughlinDecomposition X τ r W →
        ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ B : Subgroup (MulAut V), B ≤ X → IsElemAbelian p B →
          Nat.card B = p ^ pRank p X → B ≤ Subgroup.normalizer (W 0 : Set (MulAut V)) →
            ∃ y ∈ W 0, y⁻¹ * τ * y ∈ Coordinator.coreIn p (pRank p X - 1) B X


@[expose] def InputMcLaughlinTypeFacts : Prop :=
  ∀ (W : Type) [Group W] [Finite W], IsMcLaughlinGroup W →
    (Group.IsSolvable W →
      (∀ φ : MulAut W, φ ^ 3 = 1 → ∃ w : W, φ = MulAut.conj w) ∧
        Subgroup.center W = ⊥ ∧ ∀ q : ℕ, q.Prime → q ∣ Nat.card W → q = 2 ∨ q = 3) ∧
    (¬ Group.IsSolvable W →
      (IsSimpleGroup ↥(⨅ n : ℕ, derivedSeries W n) ∧
        ∃ a b : ↥(⨅ n : ℕ, derivedSeries W n), a * b ≠ b * a) ∧
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card W → q ∣ Nat.card ↥(⨅ n : ℕ, derivedSeries W n))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
