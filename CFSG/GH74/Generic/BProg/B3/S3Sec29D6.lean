module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Diagonal
public import CFSG.GH74.Generic.BProg.B3.S3L3Defs
public import CFSG.GH74.Generic.S45.LSymFix

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.Generic.S45
open scoped commutatorElement

namespace S3Sec29D6

variable {G : Type} [Group G] [Finite G] {x y : G} {K A B Q D J R : Subgroup G}

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf_two {v : G} (hv : orderOf v = 2) : IsPGroup 2 ↥(zpowers v) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv, pow_one])

omit [Finite G] in
theorem mul_self_of_orderOf_two {v : G} (hv : orderOf v = 2) : v * v = 1 := by
  have := pow_orderOf_eq_one v
  rwa [hv, pow_two] at this

end S3Sec29D6

end CFSG.GH74.Generic.BProg.B3
