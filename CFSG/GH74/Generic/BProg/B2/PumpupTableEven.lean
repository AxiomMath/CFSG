module

public import CFSG.GH74.Generic.BProg.B2.PumpupTable
public import CFSG.GH74.Generic.BProg.B2.ShapeOrders
import CFSG.GH74.Generic.S1.KL5Ord

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableEven

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.BProg.B2.ShapeOrders (SmallOrder NotJ1Order)

theorem smallOrder_of_dvd_M1 {m : ℕ}
    (h : m ∣ 2 ^ 10 * 3 ^ 5 * 5 ^ 2 * 7 * 11 * 13 * 17 * 19 * 23) : SmallOrder m := by
  refine SmallOrder.of_dvd ?_ h
  refine ⟨by decide, by decide, fun p hp hp7 h => ?_⟩
  have h1 : p ∣ 2 ^ 10 * 3 ^ 5 * 5 ^ 2 * 7 * 11 * 13 * 17 * 19 * 23 :=
    (dvd_pow_self p two_ne_zero).trans h
  have hpr : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  simp only [hp.dvd_mul] at h1
  rcases h1 with (((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1
  · have := hpr 2 Nat.prime_two (hp.dvd_of_dvd_pow h1); omega
  · have := hpr 3 Nat.prime_three (hp.dvd_of_dvd_pow h1); omega
  · have := hpr 5 Nat.prime_five (hp.dvd_of_dvd_pow h1); omega
  · have := hpr 7 (by norm_num) h1; subst this; revert h; decide
  · have := hpr 11 (by norm_num) h1; subst this; revert h; decide
  · have := hpr 13 (by norm_num) h1; subst this; revert h; decide
  · have := hpr 17 (by norm_num) h1; subst this; revert h; decide
  · have := hpr 19 (by norm_num) h1; subst this; revert h; decide
  · have := hpr 23 (by norm_num) h1; subst this; revert h; decide

theorem notJ1Order_of_not_dvd {m : ℕ} (h : ¬ 19 ∣ m) : NotJ1Order m := fun h' => h h'.2

section Certified


theorem false_of_card_small {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) {m : ℕ} (hm : Nat.card ↥H = m) (hsmall : SmallOrder m)
    (hj : NotJ1Order m) : False := by
  obtain ⟨Kt, _, hQ, hdvd⟩ := hs.exists_shape_card_dvd (m := m)
    (hm ▸ Subgroup.card_dvd_of_le inf_le_left)
  exact ShapeOrders.not_dvd_of_qShapeNS hQ hsmall hj hdvd

theorem pumpup_l28 : PumpupEmpty (fun X _ => LieModel X .PSL 2 2 3) := by
  intro N _ _ H t L hs hS
  have hc := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hS
  exact false_of_card_small hs (m := 504) (hc.trans (by decide))
    (smallOrder_of_dvd_M1 (m := 504) (by decide)) (notJ1Order_of_not_dvd (m := 504) (by decide))

theorem pumpup_l216 : PumpupEmpty (fun X _ => LieModel X .PSL 2 2 4) := by
  intro N _ _ H t L hs hS
  have hc := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hS
  exact false_of_card_small hs (m := 4080) (hc.trans (by decide))
    (smallOrder_of_dvd_M1 (m := 4080) (by decide)) (notJ1Order_of_not_dvd (m := 4080) (by decide))

theorem pumpup_l34 : PumpupEmpty (fun X _ => LieModel X .PSL 3 2 2) := by
  intro N _ _ H t L hs hS
  have hc := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hS
  exact false_of_card_small hs (m := 20160) (hc.trans (by decide))
    (smallOrder_of_dvd_M1 (m := 20160) (by decide)) (notJ1Order_of_not_dvd (m := 20160) (by decide))

theorem pumpup_u34 : PumpupEmpty (fun X _ => LieModel X .PSU 3 2 2) := by
  intro N _ _ H t L hs hS
  have hc := CFSG.GH74.Generic.S1.kl5_card_mul_gcd_psu_three
    (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hS)
  exact false_of_card_small hs (m := 62400) (by norm_num at hc; exact hc)
    (smallOrder_of_dvd_M1 (m := 62400) (by decide)) (notJ1Order_of_not_dvd (m := 62400) (by decide))

theorem pumpup_sz8 : PumpupEmpty (fun X _ => LieModel X .twistedB2 0 2 3) := by
  intro N _ _ H t L hs hS
  have hc := CFSG.GH74.card_of_lieModel_twistedB2 hS
  exact false_of_card_small hs (m := 29120) (hc.trans (by decide))
    (smallOrder_of_dvd_M1 (m := 29120) (by decide)) (notJ1Order_of_not_dvd (m := 29120) (by decide))

end Certified

end CFSG.GH74.Generic.BProg.B2.PumpupTableEven
