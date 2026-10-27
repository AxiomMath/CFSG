module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Kill
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG Blueprint

theorem ivk73_j1 :
    Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .J1) := by
  intro N _ _ L K Q h hJ
  obtain ⟨e0⟩ := hJ
  let e : ↥L ≃* CFSG.Open.walterJ1 := e0.trans CFSG.Walter.walterJ1EquivNative.symm
  obtain ⟨E, -, hc⟩ := h.exists_aut_rank_four
  have hin := GHInv.all_inner_of_mulEquiv e CFSG.Walter.J1Props.J3_aut
  have hcard : Nat.card (MulAut ↥L) = 175560 := by
    rw [GHInv.card_mulAut_eq_card_of_inner h.center_L_eq_bot hin, Nat.card_congr e.toEquiv]
    exact CFSG.Walter.J1Props.card_walterJ1
  have hdvd : 16 ∣ Nat.card (MulAut ↥L) := hc ▸ Subgroup.card_subgroup_dvd_card E
  rw [hcard] at hdvd
  omega

end CFSG.GH74.GLS.IVK
