module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bRows

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def CFProp23L34 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row514 →
    ∀ z : H, z ∈ h.D → (∀ s ∈ h.S, s * z = z * s) → orderOf z = 2 →
      ∃ g ∈ h.K, ∃ y ∈ h.B, g⁻¹ * h.a * g = h.a * z * y

@[expose] def CFL34CoverRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Group.IsPerfect Y → Nat.card (center Y) = 2 →
    Blueprint.LieModel (Y ⧸ center Y) .PSL 3 2 2 → ∀ l : Y, l ^ 2 ∈ center Y →
      ∃ E : Subgroup Y, E ≤ centralizer ({l} : Set Y) ∧ (∀ e ∈ E, e ^ 2 = 1) ∧ Nat.card E = 32

@[expose] def CFL34CoverOut : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Group.IsPerfect Y → Nat.card (center Y) = 2 →
    Blueprint.LieModel (Y ⧸ center Y) .PSL 3 2 2 →
    ∀ R : Subgroup (MulAut Y), IsPGroup 2 R →
      ∀ u ∈ R, ∀ v ∈ R, ⁅u, v⁆ ∈ (MulAut.conj : Y →* MulAut Y).range

@[expose] def CFAutL2Rank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (Blueprint.LieModel Y .PSL 2 5 1 ∨ Blueprint.LieModel Y .PSL 2 7 1) →
    ∀ E : Subgroup (MulAut Y), (∀ e ∈ E, e ^ 2 = 1) → Nat.card E ≤ 4

end CFSG.ComponentClassification.GSThmB
