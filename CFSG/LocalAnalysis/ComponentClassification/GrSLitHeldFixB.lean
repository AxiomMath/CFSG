module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixCore
public import CFSG.Sporadic.SmallOddCore.HeLocal

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

theorem not_isPComponent_centralizer_heT1P (L : Subgroup ↥(centralizerIn heP heT1P)) :
    ¬ IsPComponent 2 L := by
  intro hL
  have hO : pPrimeCore 2 (centralizerIn heP heT1P) = ⊥ := by
    rw [pPrimeCore_two_eq_oddCore]
    exact heInner1_oddCore card_heP_cent1
  exact Sporadic.SmallOddCore.heC1_no_component _
    (LocalCores.isComponent_map_mulEquiv
      (MulEquiv.subgroupCongr Sporadic.SmallOddCore.heInnerGrp1_eq.symm)
      (isComponent_of_isPComponent hO hL))

end CFSG.ComponentClassification.GrSLit.HeldFix
