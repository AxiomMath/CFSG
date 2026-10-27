module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.Components
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.Sporadic.SuzOddCore.CTIComponents

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint

theorem sporOddComps_Suz
    : SporOddComps .Suz :=
  fun _ _ _ _ _ e t ht B hB _ => by
    rw [Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t ht B hB]
    exact not_oddLieOrder_L34

theorem sporOddComps_ONan
    : SporOddComps .ONan :=
  fun _ _ _ _ _ e t ht B hB _ => by
    rw [Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
      ⟨e⟩ t ht B hB]
    exact not_oddLieOrder_L34

theorem sporOddComps_Co1
    : SporOddComps .Co1 :=
  fun S _ _ _ _ e t ht B hB _ => by
    rw [(RestrictedStd.Spor.co1LocalComponentsInput_holds S e t ht B hB).1]
    exact not_oddLieOrder_G24

theorem sporOddComps_Co2
    : SporOddComps .Co2 :=
  fun _ _ _ _ _ e t ht B hB _ =>
    absurd hB (Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e t ht B)

theorem sporOddComps_Co3
    : SporOddComps .Co3 :=
  fun _ _ _ _ _ e t ht B hB _ => by
    have h := RestrictedStd.Spor.co3_inner_comps e t ht B hB
    simp only [RestrictedStd.Spor.co3Orders, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;> rw [h]
    · exact not_oddLieOrder_Sp62
    · exact not_oddLieOrder_M12

theorem sporOddComps_Fi22
    : SporOddComps .Fi22 :=
  fun _ _ _ _ _ e t ht B hB _ => by
    rw [Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order
      e t ht B hB]
    exact not_oddLieOrder_U62

theorem sporOddComps_Fi23
    : SporOddComps .Fi23 :=
  fun _ _ _ _ _ e t ht B hB _ => by
    have h := RestrictedStd.Spor.fi23_inner_comps e t ht B hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;> rw [h]
    · exact not_oddLieOrder_Fi22
    · exact not_oddLieOrder_U62

open CFSG.Sporadic.FischerOddCore in
theorem sporOddComps_Fi24Prime
    : SporOddComps .Fi24Prime :=
  fun _ _ _ _ _ e t ht B hB _ => by
    have h :=
      CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht B hB
    rw [h.1]
    exact not_oddLieOrder_Fi22

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
