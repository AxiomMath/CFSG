module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.Quasithin.Background.F918Z4bAut

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter CFSG.Quasithin
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped commutatorElement

theorem innAutDerived_le_stdPinnedPSL2_inndiag (K : Type) [Field K] [Finite K] :
    innAutDerived (PSL2 K) ≤ (stdPinnedPSL2 K).inndiag := by
  refine sup_le (stdPinnedPSL2 K).inn_le ?_
  rw [commutator_def, Subgroup.commutator_le]
  intro α _ β _
  apply mem_range_pglAction_of_autFieldPart_eq_one
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K _ _)

theorem innAutDerived_le_comap_stdPinnedPSL2_inndiag (K : Type) [Field K] [Finite K]
    {Y : Type*} [Group Y] (e : Y ≃* PSL2 K) :
    innAutDerived Y ≤ ((stdPinnedPSL2 K).comap e).inndiag := by
  intro α hα
  rw [PinnedAut.mem_comap_inndiag]
  exact innAutDerived_le_stdPinnedPSL2_inndiag K ((mem_innAutDerived_congr e).2 hα)

end CFSG.HardMathSupport.Solomon.Coordinator
