module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem innAutDerived_le_linearAutGroup {n : ℕ} {F : Type} [Field F] [Finite F] (hn : 3 ≤ n) :
    innAutDerived (projectiveSL n F) ≤ linearAutGroup n F := by
  refine sup_le ((stdPinnedPSL n F).inn_le) ?_
  rw [commutator_def, Subgroup.commutator_le]
  intro α _ β _
  rw [commutatorElement_def]
  exact OuterDerived.commutator_mem_linearAutGroup hn α β

end CFSG.HardMathSupport.Solomon.Coordinator
