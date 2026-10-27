module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovCfg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L34
public import CFSG.GH74.GLS.LU.Local.A3Reduce2
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open CFSG.ComponentClassification.PSL3Four (S_le_R nonempty_equiv_of_stated)
local notation "S42" => CFSG.ComponentClassification.PSL3Four.S
local notation "R42" => CFSG.ComponentClassification.PSL3Four.R

theorem ivk93cov_l34 :
    Ivk93CovEmpty (fun X _ => LieModel X .PSL 3 2 2) := by
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  obtain ⟨θ⟩ := nonempty_equiv_of_stated J hst
  have hcard := GHInv.card_centralizer_eq_centralizerIn S42 θ x
  have hx2 : orderOf ((θ x : ↥S42) : Equiv.Perm (Fin 42)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hc.ord
  have hxR : ((θ x : ↥S42) : Equiv.Perm (Fin 42)) ∈ R42 := S_le_R (θ x).2
  rcases l34_inv_cases hxR hx2 with ⟨c, hc', hce, h64⟩ | ⟨c, hc', hce, h168⟩ | ⟨c, hc', hce, h60⟩ |
    ⟨c, hc', hce, h72⟩
  · exact hc.false_of_card_cent_lt (by rw [hcard]; exact lt_of_eq_of_lt h64 (by norm_num))
  · exact hc.false_of_card_cent_lt (by rw [hcard]; exact lt_of_eq_of_lt h168 (by norm_num))
  · exact hc.false_of_card_cent_lt (by rw [hcard]; exact lt_of_eq_of_lt h60 (by norm_num))
  · exact hc.false_of_card_cent_lt (by rw [hcard]; exact lt_of_eq_of_lt h72 (by norm_num))

end CFSG.GH74.GLS.IVK.Proofs2
