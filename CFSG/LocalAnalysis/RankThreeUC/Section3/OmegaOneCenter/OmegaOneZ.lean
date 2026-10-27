module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section3

namespace OmegaOneCenter

open Subgroup

variable {G : Type} [Group G]

def omegaOneZ (p : ℕ) (P : Subgroup G) : Subgroup G :=
  closure {x : G | x ∈ P ∧ x ∈ centralizer (P : Set G) ∧ x ^ p = 1}

end OmegaOneCenter

end Section3

end CFSG.LocalAnalysis.RankThreeUC
