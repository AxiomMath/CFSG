module

public import CFSG.Blueprint.Catalog
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93G2Sylow

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint

section GTwoFive


theorem not_two_dvd_card_centralizer_of_lieModel_G2_five {J : Type} [Group J] [Finite J]
    (hJ : LieModel J .G2 0 5 1) {x : J} (hx : orderOf x = 7) :
    ¬ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) := by
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({x} : Set J)) 2 h2
  have hz' : orderOf (z : J) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hxz : x ∈ Subgroup.centralizer ({(z : J)} : Set J) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp z.2).symm
  have h7 := hx ▸ Subgroup.orderOf_dvd_natCard _ hxz
  rw [CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt.g2_cent_card Nat.prime_five (by norm_num) hJ _ hz']
    at h7
  norm_num at h7

end GTwoFive

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
