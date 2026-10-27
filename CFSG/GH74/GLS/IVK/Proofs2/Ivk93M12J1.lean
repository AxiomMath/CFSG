module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Crit
public import CFSG.Walter.J1Props.Aut
public import CFSG.Walter.Models

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint

theorem ivk93m12_j1 :
    Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .J1) := by
  intro J _ _ hJ y D
  obtain ⟨e0⟩ := hJ
  let e : J ≃* CFSG.Open.walterJ1 := e0.trans CFSG.Walter.walterJ1EquivNative.symm
  have hsurj : Function.Surjective
      (MulAut.conj : CFSG.Open.walterJ1 →* MulAut CFSG.Open.walterJ1) := by
    intro φ
    obtain ⟨g, hg⟩ := CFSG.Walter.J1Props.J3_aut φ
    exact ⟨g, hg.symm⟩
  have h1 : Nat.card (MulAut CFSG.Open.walterJ1) ∣ Nat.card CFSG.Open.walterJ1 :=
    Subgroup.card_dvd_of_surjective hsurj
  rw [CFSG.Walter.J1Props.J1_card] at h1
  have h2 : Nat.card (MulAut J) = Nat.card (MulAut CFSG.Open.walterJ1) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  refine D.false_of_card_aut fun h => ?_
  rw [h2] at h
  have h3 := h.trans h1
  norm_num at h3

end CFSG.GH74.GLS.IVK.Proofs2
