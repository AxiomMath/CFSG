module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQBCentOm6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQBCentZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L511Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactQBCent6_holds : Asc82FactQBCent6 := by
  intro G _ _ L z hL Q₁ Q₂ hQ₁ hQ₂ _ _ _ hcard hz hint B hBr hB _ hBZ y hyN _ hyB
  have hBL : B ≤ L := fun b hb => (Subgroup.mem_inf.mp (hBr hb)).1
  exact fx_qb_not_mem_centralizer_of_sq hQ₁ hQ₂ hcard hz hint
    (fx_qb_sq_mem_centralizer_of_om6z2 hL hBL hB hBZ.le hyN hyB)

end CFSG.OddStandard.SmallF3.Omega
