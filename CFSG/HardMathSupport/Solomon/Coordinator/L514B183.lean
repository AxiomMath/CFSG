module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514BBalance
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification Subgroup

theorem lemma514Cover_input18_3_4G_of_schreier (hS : CatalogueRelativeB.CatalogueSchreier) :
    LocalBalance.Lemma514CoverNs.Input18_3_4G := by
  intro G _ _ hKP D E hE hDE J hJ
  have hp : Nat.Prime 3 := Nat.prime_three
  have hEp : IsPGroup 3 ↥E := isPGroup_of_isElemAbelian' hE
  have hEX : E ≤ Subgroup.centralizer (D : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun d hd =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨d, hDE hd⟩ ⟨e, he⟩)
  have hCE : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.centralizer_le hDE
  have hJ' : GLAPComponent 3 (Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (E : Set G))
      J := by
    rw [inf_eq_right.2 hCE]
    exact hJ
  have hJL : J ≤ GLAPLayer 3 (Subgroup.centralizer (D : Set G)) := by
    refine (le_sSup hJ' : J ≤ GLAPLayer 3 (Subgroup.centralizer (D : Set G) ⊓
      Subgroup.centralizer (E : Set G))).trans ?_
    by_cases hM : Subgroup.centralizer (D : Set G) = ⊤
    · rw [hM, top_inf_eq]
      exact l514b_glaPLayer_centralizer_le_top hS hKP hEp
    · exact i183_glaPLayer_inf_centralizer_le hS (isKGroup_of_isKProper hKP hM) hp hEX hEp
  exact ⟨i183Family 3 (Subgroup.centralizer (D : Set G)) J, fun L hL => hL.1,
    i183_iSup_family_eq hp hJ' hJL,
    fun L hL e he => i183_gLBConj_mem_family hEX (hJ'.1.trans inf_le_right) hL he,
    fun L hL L' hL' => i183_transitive hp hEX hEp hJ' hJL hL hL'⟩

end CFSG.HardMathSupport.Solomon.Coordinator
