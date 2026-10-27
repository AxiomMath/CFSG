module

public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt43E

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

@[expose] def AutFactB : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ) (X : Subgroup Y), p.Prime → C43b p X →
    ∀ y : Y, y ∈ centralizer (X : Set Y) → Nat.Coprime (orderOf y) p →
      y ∈ centralizer ((ncl X : Subgroup Y) : Set Y)

@[expose] def AutFactCOdd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ) (z : Y) (X : Subgroup Y), p.Prime → p ≠ 2 → C43c z p X →
    ∀ y : Y, y ∈ centralizer (X : Set Y) → Nat.Coprime (orderOf y) p →
      y ∈ centralizer ((ncl X : Subgroup Y) : Set Y)

@[expose] def AutFactE : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X : Subgroup Y), C43e X →
    ∀ y : Y, y ∈ centralizer (X : Set Y) → Odd (orderOf y) → Nat.Coprime (orderOf y) 3 →
      y ∈ centralizer ((ncl X : Subgroup Y) : Set Y)

@[expose] def AutFactD1 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (k : Kind) (z : Y) (X : Subgroup Y), C43d1 k z X →
    ∀ E : Subgroup Y, E ≤ centralizer (X : Set Y) → Odd (Nat.card ↥E) → ¬ 3 ∣ Nat.card ↥E →
      (∀ i ∈ ncl X ⊓ centralizer ({z} : Set Y), ∀ e ∈ E, i * e * i⁻¹ ∈ E) →
        E ≤ centralizer ((ncl X : Subgroup Y) : Set Y)

end CFSG.GH74.GLS.Stage2.Signalizer.L46E
