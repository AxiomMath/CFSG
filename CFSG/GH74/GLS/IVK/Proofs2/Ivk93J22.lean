module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Model2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95J2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor
  CFSG.GH74.GLS.IVK

theorem ivk93_j22 :
    Ivk93Empty2 (fun X _ => NativeSporadic.IsSporadic X .J2) := by
  refine ivk93_empty2_of_cfg fun J _ _ hJ x _ _ _ _ _ hc => ?_
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.J2 := e
  let θ : J ≃* ↥j2P := e'.trans j2PermEquiv
  rcases j2_inv_cases ((θ x : ↥j2P) : Equiv.Perm (Fin 315)) (θ x).2
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hc.ord) with
    ⟨-, hcard⟩ | ⟨g, hg, hgt⟩
  · have hC : Nat.card ↥(centralizer ({x} : Set J)) = 1920 := by
      rw [GHInv.card_centralizer_eq_centralizerIn j2P θ x]
      exact hcard
    exact hc.false_of_pair_card (by rw [hC]; norm_num)
  · exact hc.false_of_model_class j2_model θ hg hgt

end CFSG.GH74.GLS.IVK.Proofs2
