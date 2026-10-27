module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepHStmts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def HasEp2 (p : ℕ) (Y : Type) [Group Y] : Prop :=
  ∃ E : Subgroup Y, Nat.card ↥E = p ^ 2 ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x ^ p = 1

@[expose] def Comp5m2 (Fd : ℕ → (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (r p : ℕ) (Y : Type) [Group Y] [Finite Y], r.Prime → r ≠ 2 → p.Prime → 5 ≤ p → r ≠ p →
    Fd r Y → HasEp2 p Y → ∀ y g : Y, orderOf y = p →
      (∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, y * x * y⁻¹ ∈ E) → E = ⊥) →
      PairSL2 p y g →
      ∃ L : Subgroup Y, L ≠ ⊤ ∧ IsQuasisimple ↥L ∧ OddChev r (↥L ⧸ center ↥L) ∧
        y ∈ normalizer (L : Set Y) ∧ ⁅L, zpowers y⁆ ≠ ⊥

@[expose] def Comp5m1 (Fd : ℕ → (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (r p : ℕ) (Y : Type) [Group Y] [Finite Y], r.Prime → r ≠ 2 → p.Prime → 5 ≤ p → r ≠ p →
    Fd r Y → ¬ HasEp2 p Y → ∀ y g : Y, orderOf y = p →
      (∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, y * x * y⁻¹ ∈ E) → E = ⊥) →
      PairSL2 p y g →
      ∃ L : Subgroup Y, L ≠ ⊤ ∧ IsQuasisimple ↥L ∧ OddChev r (↥L ⧸ center ↥L) ∧
        y ∈ normalizer (L : Set Y) ∧ ⁅L, zpowers y⁆ ≠ ⊥

theorem comp5_of_split {Fd : ℕ → (Y : Type) → [Group Y] → Prop} (h2 : Comp5m2 Fd)
    (h1 : Comp5m1 Fd) : Comp5 Fd := by
  intro r p Y _ _ hr hr2 hp hp5 hrp hY y g hy hE hJ
  by_cases hm : HasEp2 p Y
  · exact h2 r p Y hr hr2 hp hp5 hrp hY hm y g hy hE hJ
  · exact h1 r p Y hr hr2 hp hp5 hrp hY hm y g hy hE hJ

structure Comp5m2Types : Prop where
  l3 : Comp5m2 FL3d
  u3 : Comp5m2 FU3d
  sp4 : Comp5m2 FSp4d
  g2 : Comp5m2 FG2d
  d4 : Comp5m2 FD4d
  l4 : Comp5m2 FL4d
  u4 : Comp5m2 FU4d
  ree : Comp5m2 FReed

structure Comp5m1Types : Prop where
  l3 : Comp5m1 FL3d
  u3 : Comp5m1 FU3d
  sp4 : Comp5m1 FSp4d
  g2 : Comp5m1 FG2d
  d4 : Comp5m1 FD4d
  l4 : Comp5m1 FL4d
  u4 : Comp5m1 FU4d
  ree : Comp5m1 FReed

theorem comp5Types_of_split (h2 : Comp5m2Types) (h1 : Comp5m1Types) : Comp5Types where
  l3 := comp5_of_split h2.l3 h1.l3
  u3 := comp5_of_split h2.u3 h1.u3
  sp4 := comp5_of_split h2.sp4 h1.sp4
  g2 := comp5_of_split h2.g2 h1.g2
  d4 := comp5_of_split h2.d4 h1.d4
  l4 := comp5_of_split h2.l4 h1.l4
  u4 := comp5_of_split h2.u4 h1.u4
  ree := comp5_of_split h2.ree h1.ree

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
