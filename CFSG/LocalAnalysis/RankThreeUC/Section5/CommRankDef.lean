module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def commRank {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (t : G) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.range (ρ t - 1))

end Section5

end CFSG.LocalAnalysis.RankThreeUC
