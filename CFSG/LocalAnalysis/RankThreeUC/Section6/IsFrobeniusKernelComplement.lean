module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section6

open CFSG.Open

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

def IsIrreducibleUnder (L V : Subgroup G) : Prop :=
  V ≠ ⊥ ∧ ∀ W : Subgroup G, W ≤ V → L ≤ Subgroup.normalizer (W : Set G) → W = ⊥ ∨ W = V

end Section6

end CFSG.LocalAnalysis.RankThreeUC
