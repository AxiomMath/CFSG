module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

structure FaithfulPrimeFieldKGroupModule (G : Type) [Group G] [Finite G] (p : ℕ)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ρ : Representation (ZMod p) G V) :
    Prop where
  kGroup : CFSG.Open.IsKGroup G
  prime : p.Prime
  faithful : Function.Injective ρ

end CFSG.LocalAnalysis.RankThreeUC
