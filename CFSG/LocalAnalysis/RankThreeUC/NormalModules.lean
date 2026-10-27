module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Subgroup

variable {G : Type} [Group G]

def normalElemAbelian2 (M : Subgroup G) : Set (Subgroup G) :=
  {V | V ≠ ⊥ ∧ CFSG.Assembly.IsElemAbelian 2 V ∧ V ≤ M ∧ M ≤ normalizer (V : Set G)}

def normalizerCentralizerIn (M T V : Subgroup G) : Subgroup G :=
  M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)

def normalElemAbelian2One (M T : Subgroup G) : Set (Subgroup G) :=
  {V | V ∈ normalElemAbelian2 M ∧
    ∀ N : Subgroup G, CFSG.Open.rankThreeIsMaxTwoLocal N → normalizerCentralizerIn M T V ≤ N → N = M}

theorem mem_normalElemAbelian2 {M V : Subgroup G} :
    V ∈ normalElemAbelian2 M ↔
      V ≠ ⊥ ∧ CFSG.Assembly.IsElemAbelian 2 V ∧ V ≤ M ∧ M ≤ normalizer (V : Set G) := Iff.rfl

theorem normalElemAbelian2One_subset (M T : Subgroup G) :
    normalElemAbelian2One M T ⊆ normalElemAbelian2 M := fun _ h => h.1

end CFSG.LocalAnalysis.RankThreeUC
