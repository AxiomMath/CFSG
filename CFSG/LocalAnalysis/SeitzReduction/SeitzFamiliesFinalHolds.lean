module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalElevenGLS3
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRhoMain

public section

namespace CFSG.SeitzReduction

section Reduction


theorem seitz_reduction_holds
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : CFSG.Open.standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (htype : CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L))
    (hexc : ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L))
    (hZ : Subgroup.center L = ⊥) :
    CFSG.Blueprint.NativeSporadic.SporadicRep L ∨
      CFSG.Blueprint.Recognition.Exact.EvenBNRankTwoType L ∨
      (CFSG.Blueprint.LieModel L .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel L .PSU 6 2 1 ∨
        CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1 ∨
        CFSG.Blueprint.LieModel L .POmegaPlus 4 2 1) :=
  seitz_reduction_of_split LinearPilot.lFiveFieldTildeSplitInput_holds G hnonab hK L hL hcore S hS
    htype hexc hZ

end Reduction

end CFSG.SeitzReduction
