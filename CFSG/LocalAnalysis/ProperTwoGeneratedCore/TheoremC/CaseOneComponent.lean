module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.CaseOneBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneComponent

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

namespace CoreConfig

variable {Y : Subgroup X} {u z : X}

theorem mem_pCore (hc : CoreConfig Y u z) : u ∈ CFSG.pCore 2 X := by
  exact hc.mem_twoCore

theorem pCore_pRank (hc : CoreConfig Y u z) : CFSG.Open.pRank 2 (CFSG.pCore 2 X) = 1 := by
  exact hc.twoCore_pRank

theorem center_mem_centralizer (hc : CoreConfig Y u z) (S : Set X) :
    u ∈ Subgroup.centralizer S :=
  Subgroup.mem_centralizer_iff.mpr fun y _ => (hc.commute_center y).eq

variable (hc : CoreConfig Y u z) {J : Subgroup X} (hJ : CFSG.IsComponent J) (huJ : u ∉ J)
include hc hJ huJ

theorem component_isSimpleGroup : IsSimpleGroup J :=
  component_isSimpleGroup_of_not_mem hc.oddCore_eq_bot hc.center hc.order hc.mem_pCore
    hc.pCore_pRank hJ huJ

theorem component_two_le_pRank : 2 ≤ CFSG.Open.pRank 2 J :=
  component_two_le_pRank_of_not_mem hc.oddCore_eq_bot hc.center hc.order hc.mem_pCore
    hc.pCore_pRank hJ huJ

theorem component_characteristic : J.Characteristic := by
  obtain ⟨P, hPY, hcore, -, -⟩ := hc.sylow
  exact proper_full_core_high_rank_component_characteristic P Y hc.ne_top hPY hcore J
    ((CFSG.isComponent_iff_open J).mp hJ) (hc.component_two_le_pRank hJ huJ)

theorem component_normal : J.Normal := by
  have := hc.component_characteristic hJ huJ
  infer_instance

theorem component_not_le : ¬ J ≤ Y := by
  obtain ⟨P, hPY, hcore, -, -⟩ := hc.sylow
  have := hc.component_normal hJ huJ
  exact normal_rank_two_not_le_overgroup P Y hc.ne_top hPY hcore J
    (hc.component_two_le_pRank hJ huJ)

theorem component_centralizer_pRank_le_one :
    CFSG.Open.pRank 2 (Subgroup.centralizer (J : Set X)) ≤ 1 := by
  obtain ⟨P, hPY, hcore, -, -⟩ := hc.sylow
  have := hc.component_normal hJ huJ
  exact normal_rank_two_centralizer_rank_le_one P Y hc.ne_top hPY hcore J
    (hc.component_two_le_pRank hJ huJ)

end CoreConfig

end CFSG.ProperTwoGeneratedCore.TheoremC
