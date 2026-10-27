module

public import CFSG.GH74.GLS.Bg.TwoGroups.Basic
public import CFSG.GH74.Uniqueness.SU.SU1TwoRank

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

theorem ig10_24_25 {G : Type} [Group G] [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S)
    (h8 : 8 < Nat.card S) {x : G} (hxS : x ∈ S)
    (hx : Nat.card ↥(S ⊓ centralizer ({x} : Set G)) ≤ 4) : Open.pRank 2 S ≤ 2 :=
  pRank_two_le_two_of_small_centralizer CFSG.GH74.GLS.Bg.TwoGroups.ig_9_16 hS h8 hxS hx

end CFSG.GH74.Uniqueness.SU.SU1
