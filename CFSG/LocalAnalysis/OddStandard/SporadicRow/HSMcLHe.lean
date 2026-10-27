module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.Components
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporDataA

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint

theorem sporOddComps_HS
    : SporOddComps .HS :=
  fun S _ _ _ _ e t ht B hB htB => by
    obtain ⟨hs, ⟨a, b, hab⟩, -⟩ :=
      Sporadic.SmallOddCore.cti_hs_involution_local_components_simple_order_360 ⟨e⟩ ht
        (isComponentOf_map hB)
    let eB : ↥B ≃* ↥(B.map (centralizer ({t} : Set S)).subtype) :=
      B.equivMapOfInjective _ (centralizer ({t} : Set S)).subtype_injective
    have : IsSimpleGroup ↥(B.map (centralizer ({t} : Set S)).subtype) := hs
    have : IsSimpleGroup ↥B := eB.isSimpleGroup
    refine absurd htB (selfCent_not_mem_of_simple ht inferInstance
      ⟨eB.symm a, eB.symm b, fun h => hab ?_⟩)
    have := congrArg eB h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem sporOddComps_McL
    : SporOddComps .McL :=
  fun S _ _ _ _ e t ht B hB _ => by
    obtain ⟨θ⟩ := RestrictedStd.Spor.mcl_inner_comps e t ht B hB
    rw [Nat.card_congr θ.toEquiv, Sporadic.SmallOddCore.card_mclX]
    exact not_oddLieOrder_L34

theorem sporOddComps_He
    : SporOddComps .He :=
  fun S _ _ _ _ e t ht B hB _ => by
    have h := Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order
      ⟨e⟩ ht (isComponentOf_map hB)
    rw [card_quotient_center_map] at h
    rw [h]
    exact not_oddLieOrder_L34

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
