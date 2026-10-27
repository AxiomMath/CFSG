module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviInputs
public import CFSG.HardMathSupport.Malle.OvergroupTransport.CentralQuotient
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient

public section

namespace CFSG.GroupTheory

open CFSG.HardMathSupport.Malle.OvergroupTransport

theorem gomiChevRankOneOvergroups_of_normalizerMaximal
    (h : ∀ (Y : Type) [Group Y] [Finite Y], (IsGomiL2 Y ∨ IsGomiU3 Y ∨ IsGomiSz Y) →
      ∀ U : Sylow 2 Y, NormalizerMaximal (U : Subgroup Y)) :
    GomiChevRankOneOvergroups := by
  intro G _ _ T L Q hT hL hrank hQ1 hQ2
  let Y := ↥L ⧸ Subgroup.center ↥L
  let π := QuotientGroup.mk' (Subgroup.center ↥L)
  let U' := T.subgroupOf L
  let Ū := U'.map π
  have hU : CFSG.ABGLocalTools.IsSylowOf 2 U' ⊤ := (isSylowOf_top_subgroupOf_iff hT.le).2 hT
  have hU' : CFSG.ABGLocalTools.IsSylowOf 2 Ū ⊤ :=
    isSylowOf_top_map_of_surjective (QuotientGroup.mk'_surjective _) hU
  have hp : IsPGroup 2 Ū := (CFSG.ABGLocalTools.isSylowOf_iff.1 hU').2.1
  have hi : ¬ 2 ∣ Ū.relIndex ⊤ := (CFSG.ABGLocalTools.isSylowOf_iff.1 hU').2.2
  have hi' : ¬ 2 ∣ Ū.index := by simpa [Subgroup.relIndex_top_right] using hi
  have hmax : NormalizerMaximal Ū := h Y hrank (hp.toSylow hi')
  have hmax' : NormalizerMaximal U' :=
    NormalizerMaximal.of_quotient_center (Subgroup.center ↥L) le_rfl hL.coprime_card_center
      hU.isPGroup hmax
  exact hmax_of_normalizerMaximal_subgroupOf hT.le hmax' Q hQ2 hQ1

end CFSG.GroupTheory
