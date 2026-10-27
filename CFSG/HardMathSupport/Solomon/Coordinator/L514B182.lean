module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514BBalance
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification

section Core

variable {G : Type} [Group G] [Finite G]

theorem l514b_layer_layer_inf (M E : Subgroup G)
    (hbal : GLAPLayer 3 (M ⊓ Subgroup.centralizer (E : Set G)) ≤ GLAPLayer 3 M) :
    GLAPLayer 3 (GLAPLayer 3 M ⊓ Subgroup.centralizer (E : Set G)) =
      GLAPLayer 3 (M ⊓ Subgroup.centralizer (E : Set G)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set A : Subgroup G := M ⊓ Subgroup.centralizer (E : Set G) with hA
  set B : Subgroup G := GLAPLayer 3 M ⊓ Subgroup.centralizer (E : Set G) with hB
  have hBA : B ≤ A := le_inf (inf_le_left.trans (i183_glaPLayer_le 3 M)) inf_le_right
  have hnorm : (B.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBA]
    exact fun g hg => i183_mem_normalizer_inf (i183v_le_normalizer_glaPLayer 3 M hg.1)
      (Subgroup.le_normalizer hg.2)
  apply le_antisymm
  · refine sSup_le fun J hJ => le_sSup ?_
    exact i183v_comp_up hp hJ hBA
      (isSubnormal_trans' hJ.2.1 (CFSG.Quasithin.A3.subnormal_of_normal hBA hnorm))
  · refine sSup_le fun J hJ => le_sSup ?_
    exact glaPComponent_of_le hp hJ
      (le_inf ((le_sSup hJ).trans hbal) (hJ.1.trans inf_le_right)) hBA

end Core

theorem lemma514Cover_input18_2_of_schreier (hS : CatalogueRelativeB.CatalogueSchreier) :
    LocalBalance.Lemma514CoverNs.Input18_2 := by
  intro G _ _ hKP D E hD hE hDE
  by_cases hM : Subgroup.centralizer (D : Set G) = ⊤
  · have hM' : LocalBalance.Lemma514CoverNs.CD D = ⊤ := hM
    rw [hM']
    refine l514b_layer_layer_inf _ E ?_
    rw [top_inf_eq]
    exact l514b_glaPLayer_centralizer_le_top hS hKP hE
  · have hK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (D : Set G)) :=
      isKGroup_of_isKProper hKP hM
    have hEX : E ≤ Subgroup.centralizer (D : Set G) := fun e he =>
      Subgroup.mem_centralizer_iff.2 fun d hd => hDE d hd e he
    exact l514b_layer_layer_inf _ E (i183_glaPLayer_inf_centralizer_le hS hK Nat.prime_three hEX hE)

end CFSG.HardMathSupport.Solomon.Coordinator
