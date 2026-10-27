module

public import CFSG.GH74.GLS.Stage1.Main.Out

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GH74.GLS.Stage1.Thm3.Sec8

@[expose] def RankG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), G2Term G z S → pRank 2 ↥S ≤ 3

@[expose] def RankL4U4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool), L4U4TermTypeE ε G z S →
    pRank 2 ↥S = 4

@[expose] def RankTerm7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) (w : G), Term7Out G z S q w →
    4 ≤ pRank 2 ↥S

@[expose] def B2Split : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), InB2 (HatT K) → pRank 2 ↥K ≠ 1 →
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ IsDoubleCoverOfAlt (HatT K) n ∧ 4 ≤ pRank 2 ↥K) ∨
    (IsQuasisimple (HatT K) ∧ IsL34Quotient (HatT K) ∧ Monoid.exponent ↥(center (HatT K)) = 4)

@[expose] def Gen4NoL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ K : Subgroup G,
    ¬ (IsQuasisimple (HatT K) ∧ IsL34Quotient (HatT K) ∧ Monoid.exponent ↥(center (HatT K)) = 4)

end CFSG.GH74.GLS.Stage1.Main
