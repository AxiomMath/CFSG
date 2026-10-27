module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinGlue

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG FinGlue
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer inner_normal)

namespace FinOut

theorem card_outer_le {G : Type} [Group G] [Finite G] (hc : center G = ⊥)
    (h : Nat.card (MulAut G) ≤ 2 * Nat.card G) : Nat.card (Outer G) ≤ 2 := by
  have hinn : Nat.card (inner G) = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_center' hc)).toEquiv).symm
  have hcard := (inner G).card_eq_card_quotient_mul_card_subgroup
  rw [hinn] at hcard
  have hpos : 0 < Nat.card G := Nat.card_pos
  have : Nat.card (Outer G) * Nat.card G ≤ 2 * Nat.card G := hcard ▸ h
  exact Nat.le_of_mul_le_mul_right this hpos

theorem exists_conj_of_orderOf {Y : Type} [Group Y] [Finite Y] (hO : Nat.card (Outer Y) ≤ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : MulAut Y} (hx : orderOf x = p) :
    ∃ y : Y, MulAut.conj y = x := by
  have : (inner Y).Normal := inner_normal Y
  have hfin : Finite (MulAut Y) :=
    Finite.of_injective (fun α : MulAut Y => (α : Y → Y)) DFunLike.coe_injective
  let π : MulAut Y →* Outer Y := QuotientGroup.mk' (inner Y)
  have h1 : orderOf (π x) ∣ p := by
    rw [← hx]
    exact orderOf_map_dvd π x
  have h3 : orderOf (π x) ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard (π x))).trans hO
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exact MonoidHom.mem_range.mp ((QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h))
  · have := hp.two_le
    omega

end FinOut

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
