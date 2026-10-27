module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification

theorem lbiInput18_2One_of_schreier (hS : CatalogueRelativeB.CatalogueSchreier) :
    LocalBalance.Input18_2One := by
  intro Y _ _ hK p hp E hE
  have hLN : Subgroup.centralizer (E : Set Y) ≤
      Subgroup.normalizer (GLAPLayer p (⊤ : Subgroup Y) : Set Y) := fun g _ =>
    i183v_le_normalizer_glaPLayer p ⊤ (Subgroup.mem_top g)
  have hnormal : ((GLAPLayer p (⊤ : Subgroup Y) ⊓ Subgroup.centralizer (E : Set Y)).subgroupOf
      (Subgroup.centralizer (E : Set Y))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact fun g hg => i183_mem_normalizer_inf (hLN hg) (Subgroup.le_normalizer hg)
  apply le_antisymm
  · refine sSup_le fun J hJ => le_sSup ?_
    exact i183v_comp_up hp hJ inf_le_right
      (isSubnormal_trans' hJ.2.1 (CFSG.Quasithin.A3.subnormal_of_normal inf_le_right hnormal))
  · have hbal : GLAPLayer p (Subgroup.centralizer (E : Set Y)) ≤ GLAPLayer p (⊤ : Subgroup Y) := by
      have := Fact.mk hp
      rw [i183_glaPLayer_eq, i183_glaPLayer_eq]
      exact (LBalance.l_balance_clauses hS Y hK p hp E hE).2
    refine sSup_le fun J hJ => le_sSup ?_
    exact glaPComponent_of_le hp hJ
      (le_inf ((le_sSup hJ).trans hbal) hJ.1) inf_le_right

theorem input18_2One_holds :

    LocalBalance.Input18_2One :=
  lbiInput18_2One_of_schreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds

end CFSG.HardMathSupport.Solomon.Coordinator
