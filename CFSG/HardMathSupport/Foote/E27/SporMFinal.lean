module

public import CFSG.HardMathSupport.Foote.E27.SporM
public import CFSG.HardMathSupport.Foote.E27.SporMAction
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeBDatum

public section

namespace CFSG.HardMathSupport.Foote.E27

set_option linter.unusedSectionVars false

open CFSG.AGLEmbedding.Norton.MON5_7


theorem mAct_XU_eq : MAct.XU = tbXU := Units.ext (by rw [coe_tbXU]; rfl)

theorem mAct_YU_eq : MAct.YU = tbYU := Units.ext (by rw [coe_tbYU]; rfl)

theorem three_pow_seven_dvd_card_tb :
    3 ^ 7 ∣ Nat.card (Subgroup.closure {g | g ∈ [tbXU, tbYU]}) := by
  rw [← mAct_XU_eq, ← mAct_YU_eq]
  exact MAct.three_pow_dvd_card_K


theorem e27SporAt_M : E27SporAt .M :=
  e27SporAt_M_of_local (c₁ := tbc₁) (c₂ := tbc₂) tbCommData tbb₁_conj_U tbb₂_conj_U
    three_pow_seven_dvd_card_tb

end CFSG.HardMathSupport.Foote.E27
