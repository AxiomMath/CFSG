module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.CatalogOrders
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.AnyMain
public import CFSG.LocalAnalysis.OddStandard.L2Ree.Common

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard.SmallF3Interfaces

section Certified


theorem not_sporadicRep_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : StandardSetting G L) (hQ : SmallF3LieQuotient (L ⧸ center L)) :
    ¬ SporadicRep G := by
  rintro ⟨s, ⟨e⟩⟩
  haveI hsimple : IsSimpleGroup G := hS.simple
  have hCeven : Even (Nat.card (centralizer (L : Set G))) := hS.standard.2.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(centralizer (L : Set G))) 2
      (even_iff_two_dvd.mp hCeven)
  let t : G := c
  have ht : t ∈ centralizer (L : Set G) := c.2
  have ht2 : orderOf t = 2 := (Subgroup.orderOf_coe c).trans hc
  obtain ⟨hLt, hcomp⟩ := CFSG.OddStandard.L2Ree.isComponent_of_standard hS.standard ht ht2
  have hQL : Nat.card (L ⧸ center L) ∣ Nat.card L := Subgroup.card_quotient_dvd_card (center L)
  have hQG : Nat.card (L ⧸ center L) ∣ Nat.card G := hQL.trans (Subgroup.card_subgroup_dvd_card L)
  have h5616 := le_card_of_smallF3LieQuotient hQ
  have hQle : Nat.card (L ⧸ center L) ≤ Nat.card L := Nat.le_of_dvd Nat.card_pos hQL
  obtain ⟨τ, n, p, f, hp, hp2, _hadm, hm⟩ := oddLieType hQ
  have hodd := CFSG.ComponentClassification.HarrisLit.T1.SporRow.oddLieOrder_of_lieModel hp hp2 hm
  obtain ⟨eB⟩ := CFSG.OddStandard.L2Ree.nonempty_quotient_center_subgroupOf hLt
  cases s with
  | M11 => exact not_card_dvd_card_of_isSporadic hQ (.inl ⟨e⟩) hQG
  | M12 => exact not_card_dvd_card_of_isSporadic hQ (.inr (.inl ⟨e⟩)) hQG
  | J1 => exact not_card_dvd_card_of_isSporadic hQ (.inr (.inr (.inl ⟨e⟩))) hQG
  | HS => exact not_card_dvd_card_of_isSporadic hQ (.inr (.inr (.inr ⟨e⟩))) hQG
  | J2 => have := card_le_of_isSporadic_J2 ⟨e⟩ ht2 hLt; omega
  | J3 => have := card_le_of_isSporadic_J3 ⟨e⟩ ht2 hLt; omega
  | _ =>
    exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.sporOddCompsAny_of _
      (by decide) G hS.nonab e t ht2 _ hcomp
      (by rw [Nat.card_congr eB.toEquiv]; exact hodd)

end Certified

end CFSG.OddStandard.SmallF3
