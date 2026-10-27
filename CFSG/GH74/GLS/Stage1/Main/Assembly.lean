module

public import CFSG.GH74.GLS.Stage1.Main.Out

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def Stage1OutFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std0 G → pRank 2 G = 4 → HasTwoThinConfiguration G →
    ∃ (z : G) (S : Subgroup G) (k : Kind),
      (k = Kind.psp4 ∨ (∃ ε : Bool, k = Kind.l4 ε) ∨ k = Kind.mcl ∨ k = Kind.ly) ∧
      IsCentralInvolution z ∧ CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G)) ∧
      Stage1Out G z S k

@[expose] def Stage1OutThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std0 G → pRank 2 G = 3 → HasTwoThinConfiguration G →
    ∃ (z : G) (S : Subgroup G), IsCentralInvolution z ∧
      CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G)) ∧ Stage1Out G z S Kind.g2

end CFSG.GH74.GLS.Stage1.Main
