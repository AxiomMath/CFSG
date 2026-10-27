module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.AnyDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporDataA

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint

theorem sporOddCompsAny_McL
    : SporOddCompsAny .McL :=
  fun S _ _ _ _ e t ht B hB => by
    obtain ⟨θ⟩ := RestrictedStd.Spor.mcl_inner_comps e t ht B hB
    rw [Nat.card_congr θ.toEquiv, Sporadic.SmallOddCore.card_mclX]
    exact not_oddLieOrder_L34

theorem sporOddCompsAny_He
    : SporOddCompsAny .He :=
  fun S _ _ _ _ e t ht B hB => by
    have h := Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order
      ⟨e⟩ ht (isComponentOf_map hB)
    rw [card_quotient_center_map] at h
    rw [h]
    exact not_oddLieOrder_L34

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
