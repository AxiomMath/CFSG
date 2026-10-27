module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.PComm

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

structure Core2 (E : Subgroup G) (t z : G) : Prop extends Core1 E t z where
  rp : RPData E t z
  pc : ⁅Pg E z, Pg E z⁆ = Rg t z ⊓ E

theorem core2 (c : Core1 E t z) : Core2 E t z :=
  have rp := rpData c
  ⟨c, rp, comm_P_eq c rp⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
