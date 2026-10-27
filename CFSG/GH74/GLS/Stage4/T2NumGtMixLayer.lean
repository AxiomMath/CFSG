module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLayerCore
public import CFSG.GH74.GLS.Stage4.T2NumGtMixLayerThree
public import CFSG.GH74.GLS.Stage4.T2NumGtMixTSDefs
public import CFSG.GH74.GLS.Stage4.T2P56Fin

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank

theorem ch6Mix_layer
    (hL : SDWreathedLayer)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : Ch6MixLayer := by
  intro G _ _ hStd hr Gs _ q₁ q₂ _ _ hmod z K₁ K₂ F₁ F₂ _ _ t hSet hRem p n hp hp2 hq₂p N u hz hK₁
    hK₂ hq₁ hq₂ _ hSec y hyH hyz hyp hyodd _ hya
  by_cases h3 : q₂ = 3
  · exact exists_J_three_mix hL hGA noM11Layer hStd hSet hRem hp hp2 ⟨n, hq₂p⟩ hmod h3 hz hK₁ hK₂
      hq₁ hq₂ hSec hyH hyz hyp hyodd hya
  · have hq₂3 : 3 ≤ q₂ := by
      have := hSec.loc.q₂_ge
      rw [hq₂] at this
      exact this
    have h5 : 5 ≤ q₂ := by
      rcases hSet.odd₂ with ⟨k, hk⟩
      omega
    exact exists_J_core_mix hL (LU.Local.l3Cover hGA) hStd hr hSet hRem hp hp2 ⟨n, hq₂p⟩ hmod h5
      hz hK₁ hK₂ hq₁ hq₂ hSec hyH hyz hyp hyodd hya

end CFSG.GH74.GLS.Stage4.Rest
