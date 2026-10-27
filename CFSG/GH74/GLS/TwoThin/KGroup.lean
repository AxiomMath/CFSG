module

public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentInitial.SwappedQuasisimple
public import CFSG.GH74.GLS.TwoThin.G.Pred

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

@[expose] def TwoThinKGroupVertical : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (s : H) (L I : Subgroup H) (K₀ : Type) [Group K₀],
    orderOf s = 2 → CFSG.IsComponent L → (InC2 ↥L ∨ InT2 ↥L) → conjSub s⁻¹ L = L →
    IsPCompIn 2 (centralizer ({s} : Set H)) I → I ≤ L →
    InB2 K₀ → (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → InB2 ↥L

@[expose] def TwoThinKGroupDiagonal : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (s : H) (L I : Subgroup H) (K₀ : Type) [Group K₀]
    (hAB : ⁅L, conjSub s⁻¹ L⁆ = ⊥),
    orderOf s = 2 → CFSG.IsComponent L → (InC2 ↥L ∨ InT2 ↥L) → conjSub s⁻¹ L ≠ L →
    IsPCompIn 2 (centralizer ({s} : Set H)) I → I ≤ (swapDiag hAB).range →
    InB2 K₀ → (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → InB2 ↥L

@[expose] def TwoThinKGroupFact : Prop :=
  TwoThinKGroupVertical ∧ TwoThinKGroupDiagonal

@[expose] def TwoThinKGroupVerticalQ (Q : GroupPred) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Q H → ∀ (s : H) (L I : Subgroup H) (K₀ : Type) [Group K₀],
    orderOf s = 2 → CFSG.IsComponent L → (InC2 ↥L ∨ InT2 ↥L) → conjSub s⁻¹ L = L →
    IsPCompIn 2 (centralizer ({s} : Set H)) I → I ≤ L →
    InB2 K₀ → (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → InB2 ↥L

@[expose] def TwoThinKGroupDiagonalQ (Q : GroupPred) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Q H → ∀ (s : H) (L I : Subgroup H) (K₀ : Type) [Group K₀]
    (hAB : ⁅L, conjSub s⁻¹ L⁆ = ⊥),
    orderOf s = 2 → CFSG.IsComponent L → (InC2 ↥L ∨ InT2 ↥L) → conjSub s⁻¹ L ≠ L →
    IsPCompIn 2 (centralizer ({s} : Set H)) I → I ≤ (swapDiag hAB).range →
    InB2 K₀ → (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → InB2 ↥L

@[expose] def TwoThinKGroupFactQ (Q : GroupPred) : Prop :=
  TwoThinKGroupVerticalQ Q ∧ TwoThinKGroupDiagonalQ Q

theorem TwoThinKGroupFact.toQ (h : TwoThinKGroupFact) (Q : GroupPred) : TwoThinKGroupFactQ Q := by
  refine ⟨?_, ?_⟩
  · intro H _ _ _ s L I K₀ _
    exact h.1 H s L I K₀
  · intro H _ _ _ s L I K₀ _ hAB
    exact h.2 H s L I K₀ hAB

theorem TwoThinKGroupFactQ.toFact (h : TwoThinKGroupFactQ GroupPred.trivial) :
    TwoThinKGroupFact := by
  refine ⟨?_, ?_⟩
  · intro H _ _ s L I K₀ _
    exact h.1 H trivial s L I K₀
  · intro H _ _ s L I K₀ _ hAB
    exact h.2 H trivial s L I K₀ hAB

end CFSG.GH74.GLS.TwoThin
