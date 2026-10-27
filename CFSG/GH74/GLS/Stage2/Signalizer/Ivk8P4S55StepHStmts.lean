module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Cross

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def Ord3 (Fd : ℕ → (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (r : ℕ) (Y : Type) [Group Y] [Finite Y], r.Prime → r ≠ 2 → r ≠ 3 → Fd r Y →
    ∀ b : MulAut Y, orderOf b = 3 →
      (∃ E : Subgroup Y, E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, b x ∈ E) ∨
        ∃ s : ℕ, HHObsAt 3 s Y b ∧ (s = 2 → NoR 2 Y)

@[expose] def D4Ord3 : Prop := Ord3 FD4d

structure Ord3Types : Prop where
  l3 : Ord3 FL3d
  u3 : Ord3 FU3d
  sp4 : Ord3 FSp4d
  g2 : Ord3 FG2d
  d4 : D4Ord3
  l4 : Ord3 FL4d
  u4 : Ord3 FU4d

@[expose] def OrdPInner (Fd : ℕ → (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (r p : ℕ) (Y : Type) [Group Y] [Finite Y], r.Prime → r ≠ 2 → p.Prime → 5 ≤ p → r ≠ p →
    Fd r Y → ∀ b : MulAut Y, orderOf b = p →
      (∃ E : Subgroup Y, E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, b x ∈ E) ∨
        b ∈ (MulAut.conj : Y →* MulAut Y).range

structure OrdPInnerTypes : Prop where
  l3 : OrdPInner FL3d
  u3 : OrdPInner FU3d
  sp4 : OrdPInner FSp4d
  g2 : OrdPInner FG2d
  d4 : OrdPInner FD4d
  l4 : OrdPInner FL4d
  u4 : OrdPInner FU4d
  ree : OrdPInner FReed

@[expose] def PairSL2 {Y : Type} [Group Y] (p : ℕ) (y g : Y) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
    ((∃ φ : ↥(closure ({y, g * y * g⁻¹} : Set Y)) →* ↥(StatedSL 2 F), Function.Surjective φ) ∨
      (¬ NoR 2 Y ∧ ∃ φ : ↥(closure ({y, g * y * g⁻¹} : Set Y)) →*
        (↥(StatedSL 2 F) ⧸ center ↥(StatedSL 2 F)), Function.Surjective φ))

@[expose] def Comp5 (Fd : ℕ → (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (r p : ℕ) (Y : Type) [Group Y] [Finite Y], r.Prime → r ≠ 2 → p.Prime → 5 ≤ p → r ≠ p →
    Fd r Y → ∀ y g : Y, orderOf y = p →
      (∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, y * x * y⁻¹ ∈ E) → E = ⊥) →
      PairSL2 p y g →
      ∃ L : Subgroup Y, L ≠ ⊤ ∧ IsQuasisimple ↥L ∧ OddChev r (↥L ⧸ center ↥L) ∧
        y ∈ normalizer (L : Set Y) ∧ ⁅L, zpowers y⁆ ≠ ⊥

structure Comp5Types : Prop where
  l3 : Comp5 FL3d
  u3 : Comp5 FU3d
  sp4 : Comp5 FSp4d
  g2 : Comp5 FG2d
  d4 : Comp5 FD4d
  l4 : Comp5 FL4d
  u4 : Comp5 FU4d
  ree : Comp5 FReed

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
