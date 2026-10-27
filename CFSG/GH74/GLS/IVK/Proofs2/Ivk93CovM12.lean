module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovModel
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95M12

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.M12Cover
  CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor CFSG.GH74.GLS.IVK

theorem ivk93cov_m12 :
    Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .M12) := by
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ _ _ hc => ?_
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.M12 := e
  let θ : J ≃* ↥blockGroup := e'.trans m12EquivD
  rcases m12_inv_cases ((θ x : ↥blockGroup) : Equiv.Perm (Fin 24)) (θ x).2
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hc.ord) with ⟨g, hg, hgt⟩ | h192
  · exact hc.false_of_model_class m12_model θ hg hgt
  · have hcard : Nat.card ↥(centralizer ({x} : Set J)) = 192 := by
      rw [GHInv.card_centralizer_eq_centralizerIn blockGroup θ x]
      exact h192
    exact hc.false_of_card_cent_lt (by rw [hcard]; norm_num)

end CFSG.GH74.GLS.IVK.Proofs2
