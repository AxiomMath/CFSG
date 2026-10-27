module

public import CFSG.GH74.Generic.S1.SymNbhd
public import CFSG.GH74.Generic.S45.LLift
public import CFSG.GH74.Generic.JStar2Defs
public import CFSG.GH74.Generic.JMaxThin
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def LiftCentralAt {G : Type} [Group G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  ∀ n ∈ S1.liftL x K, proj x n = 1 → ∀ l ∈ S1.liftL x K, n * l = l * n

end CFSG.GH74.Generic
