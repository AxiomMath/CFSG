module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Hyp

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G]

structure SolomonLocal (L K : Subgroup G) (u : G) : Prop where
  simpleL : IsSimpleGroup L
  nonabelianL : ∃ a b : L, a * b ≠ b * a
  u_order : orderOf u = 2
  u_mem : u ∈ L
  K_le : K ≤ L
  u_mem_centralizer_K : u ∈ centralizer (K : Set G)
  standard_in_L : standardComponentIsStandard (K.subgroupOf L)
  autCentralizer_two : twoAdic (autCentralizer L K) ≤ 2

end CFSG.EvenSporadicStandard.Solomon78
