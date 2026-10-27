module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L34
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Gen
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Bender
public import CFSG.GH74.GLS.LU.Local.A3Reduce2
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open CFSG.ComponentClassification.PSL3Four (S_le_R nonempty_equiv_of_stated)
local notation "S42" => CFSG.ComponentClassification.PSL3Four.S
local notation "R42" => CFSG.ComponentClassification.PSL3Four.R

theorem ivk95_l34 :
    Ivk95Empty (fun X _ => LieModel X .PSL 3 2 2) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  obtain ⟨θ⟩ := nonempty_equiv_of_stated J hst
  have hcard := GHInv.card_centralizer_eq_centralizerIn S42 θ z
  have hx2 : orderOf ((θ z : ↥S42) : Equiv.Perm (Fin 42)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hz.ord
  have hxR : ((θ z : ↥S42) : Equiv.Perm (Fin 42)) ∈ R42 := S_le_R (θ z).2
  rcases l34_inv_cases hxR hx2 with ⟨c, hc, hce, h64⟩ | ⟨c, hc, hce, h168⟩ | ⟨c, hc, hce, h60⟩ |
    ⟨c, hc, hce, h72⟩
  · exact hz.false_of_card_cent_dvd (N := 64) (by rw [hcard]; exact dvd_of_eq h64)
      (not_sl2_dvd_of_lt (by norm_num) (by norm_num))
  · exact hz.false_of_card_cent_dvd (N := 168) (by rw [hcard]; exact dvd_of_eq h168)
      (fun q hq => not_sl2_dvd_168 q hq)
  · exact hz.false_of_card_cent_dvd (N := 60) (by rw [hcard]; exact dvd_of_eq h60)
      (not_sl2_dvd_of_lt (by norm_num) (by norm_num))
  · exact hz.false_of_card_cent_dvd (N := 72) (by rw [hcard]; exact dvd_of_eq h72)
      (not_sl2_dvd_of_lt (by norm_num) (by norm_num))

end CFSG.GH74.GLS.IVK.Proofs2
