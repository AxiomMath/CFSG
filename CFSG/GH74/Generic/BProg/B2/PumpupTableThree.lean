module

public import CFSG.GH74.Generic.BProg.B2.PumpupTable
public import CFSG.GH74.Generic.BProg.B2.ShapeOrders
import CFSG.GH74.Generic.S3.L3ClassC2T2

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableThree

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.BProg.B2.ShapeOrders (NotJ1Order prime_cases card_statedSL4 pow_six_dvd_psu4
  pow_three_dvd_ordA pow_three_dvd_ordTwistedA three_pow_nine_dvd_ordRee)
open CFSG.Open (ordA ordTwistedA ordG2 ordRee)

@[expose] def SmallOrder3 (m : ℕ) : Prop :=
  ¬ 3 ^ 7 ∣ m ∧ ¬ 5 ^ 3 ∣ m ∧ (∀ p : ℕ, p.Prime → 7 ≤ p → ¬ p ^ 2 ∣ m) ∧ m < 12130560

theorem SmallOrder3.not_pow_dvd {m : ℕ} (hm : SmallOrder3 m) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : p = 3 → 7 ≤ e) (h5 : p = 5 → 3 ≤ e) (h7 : 7 ≤ p → 2 ≤ e) : ¬ p ^ e ∣ m := by
  intro h
  rcases prime_cases hp hp2 with rfl | rfl | h7'
  · exact hm.1 ((pow_dvd_pow 3 (h3 rfl)).trans h)
  · exact hm.2.1 ((pow_dvd_pow 5 (h5 rfl)).trans h)
  · exact hm.2.2.1 p hp h7' ((pow_dvd_pow p (h7 h7')).trans h)

theorem prime_sq_not_dvd_of_dvd {m : ℕ}
    (h : m ∣ 2 ^ 10 * 3 ^ 8 * 5 ^ 4 * 7 * 11 * 13 * 17 * 19 * 23) :
    ∀ p : ℕ, p.Prime → 7 ≤ p → ¬ p ^ 2 ∣ m := by
  intro p hp hp7 hpm
  have h1 : p ∣ 2 ^ 10 * 3 ^ 8 * 5 ^ 4 * 7 * 11 * 13 * 17 * 19 * 23 :=
    (dvd_pow_self p two_ne_zero).trans (hpm.trans h)
  have hpr : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  have h2 : p ^ 2 ∣ 2 ^ 10 * 3 ^ 8 * 5 ^ 4 * 7 * 11 * 13 * 17 * 19 * 23 := hpm.trans h
  simp only [hp.dvd_mul] at h1
  rcases h1 with (((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1
  · have := hpr 2 Nat.prime_two (hp.dvd_of_dvd_pow h1); omega
  · have := hpr 3 Nat.prime_three (hp.dvd_of_dvd_pow h1); omega
  · have := hpr 5 Nat.prime_five (hp.dvd_of_dvd_pow h1); omega
  · have := hpr 7 (by norm_num) h1; subst this; revert h2; decide
  · have := hpr 11 (by norm_num) h1; subst this; revert h2; decide
  · have := hpr 13 (by norm_num) h1; subst this; revert h2; decide
  · have := hpr 17 (by norm_num) h1; subst this; revert h2; decide
  · have := hpr 19 (by norm_num) h1; subst this; revert h2; decide
  · have := hpr 23 (by norm_num) h1; subst this; revert h2; decide

theorem not_dvd_of_qShape1_three {Kt : Type} [Group Kt] (h : QShape1 Kt) {m : ℕ}
    (hm : SmallOrder3 m) (hm0 : 0 < m) : ¬ Nat.card Kt ∣ m := by
  intro hdvd
  rcases h with ⟨F, hF, hFin, hmod, ⟨e⟩⟩ | ⟨q, F, hF, hFin, hcard, hq4, ⟨e⟩⟩
  · have hKt : Nat.card Kt = Nat.card (StatedSL 4 F) := Nat.card_congr e.toEquiv
    rw [card_statedSL4] at hKt
    have hc3 : 3 ≤ Nat.card F := by omega
    have h1 : 3 ^ 6 ≤ Nat.card F ^ 6 := Nat.pow_le_pow_left hc3 6
    have h2 : 3 ^ 2 - 1 ≤ Nat.card F ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hc3 2) 1
    have h3 : 3 ^ 3 - 1 ≤ Nat.card F ^ 3 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hc3 3) 1
    have h4 : 3 ^ 4 - 1 ≤ Nat.card F ^ 4 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hc3 4) 1
    have hge : 12130560 ≤ Nat.card Kt := by
      rw [hKt]
      calc 12130560 = 3 ^ 6 * ((3 ^ 2 - 1) * (3 ^ 3 - 1) * (3 ^ 4 - 1)) := by norm_num
        _ ≤ _ := Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.mul_le_mul h2 h3) h4)
    have := Nat.le_of_dvd hm0 hdvd
    have := hm.2.2.2
    omega
  · obtain ⟨p, f, hpp, hchar, rfl⟩ := CFSG.GH74.L5U5.exists_prime_pow_of_card_eq_sq hcard
    have hpp' : p.Prime := hpp.out
    have hKt : Nat.card Kt = Nat.card (StatedSU 4 (p ^ f) F) := Nat.card_congr e.toEquiv
    have hf : 1 ≤ f := by
      by_contra hf0
      have : f = 0 := by omega
      subst this
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hcard] at h1
      simp at h1
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      omega
    have hdvd' : Nat.card (StatedProj (StatedSU 4 (p ^ f) F)) ∣ Nat.card (StatedSU 4 (p ^ f) F) :=
      Subgroup.card_quotient_dvd_card _
    have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (n := 4) hpp' hf hcard
      (by norm_num)
    rw [CFSG.GH74.Generic.BProg.B2.ShapeOrders.prod_Icc_two_four] at h1
    have h6 : p ^ (6 * f) ∣ m := by
      rw [mul_comm 6 f, pow_mul]
      refine Dvd.dvd.trans ?_ (hdvd'.trans (hKt ▸ hdvd))
      rw [h1]
      exact pow_six_dvd_psu4 (p ^ f) (Nat.one_le_pow _ _ hpp'.pos)
    refine hm.not_pow_dvd hpp' hp2 (fun h3 => ?_) (fun _ => by omega) (fun _ => by omega) h6
    subst h3
    by_contra hlt
    have : f = 1 := by omega
    subst this
    omega

theorem not_dvd_of_qShape3_three {Kt : Type} [Group Kt] (h : QShape3 Kt) {m : ℕ}
    (hm : SmallOrder3 m) (hm0 : 0 < m) : ¬ Nat.card Kt ∣ m := by
  intro hdvd
  obtain ⟨p, f, hp, hp2, hq, hL⟩ := h
  have hf : 1 ≤ f := by
    by_contra hf0
    have : f = 0 := by omega
    subst this
    simp at hq
  have hdvd3 : p ^ (3 * f) ∣ m := by
    rw [mul_comm 3 f, pow_mul]
    refine Dvd.dvd.trans ?_ hdvd
    rcases hL with hL | hL
    · rw [card_of_lieModel_PSL (by norm_num) hL]
      exact pow_three_dvd_ordA (p ^ f)
    · rw [card_of_lieModel_PSU (by norm_num) hp2 hL]
      exact pow_three_dvd_ordTwistedA (p ^ f)
  rcases prime_cases hp hp2 with rfl | rfl | h7
  · by_cases hf3 : 3 ≤ f
    · exact hm.1 ((pow_dvd_pow 3 (by omega : 7 ≤ 3 * f)).trans hdvd3)
    · have hf2 : f = 2 := by
        by_contra hne
        have : f = 1 := by omega
        subst this
        simp at hq
      subst hf2
      have hge : 12130560 ≤ Nat.card Kt := by
        rcases hL with hL | hL
        · rw [card_of_lieModel_PSL (by norm_num) hL,
            show 3 - 1 = 2 by norm_num, CFSG.GH74.Generic.S3.L3Ord.ordA_two]
          norm_num
        · rw [card_of_lieModel_PSU (by norm_num) hp2 hL,
            show 3 - 1 = 2 by norm_num, CFSG.GH74.Generic.S3.L3Ord.ordTwistedA_two]
          norm_num
      have := Nat.le_of_dvd hm0 hdvd
      have := hm.2.2.2
      omega
  · exact hm.2.1 ((pow_dvd_pow 5 (by omega : 3 ≤ 3 * f)).trans hdvd3)
  · exact hm.2.2.1 p hp h7 ((pow_dvd_pow p (by omega : 2 ≤ 3 * f)).trans hdvd3)

theorem smallOrder3_of_dvd {m : ℕ}
    (hdvd : m ∣ 2 ^ 10 * 3 ^ 8 * 5 ^ 4 * 7 * 11 * 13 * 17 * 19 * 23) (h3 : ¬ 3 ^ 7 ∣ m)
    (h5 : ¬ 5 ^ 3 ∣ m) (hlt : m < 12130560) : SmallOrder3 m :=
  ⟨h3, h5, prime_sq_not_dvd_of_dvd hdvd, hlt⟩

theorem notJ1Order_of_not_dvd {m : ℕ} (h : ¬ 19 ∣ m) : NotJ1Order m := fun h' => h h'.2

section Certified


theorem not_dvd_of_qShape4_three {Kt : Type} [Group Kt] (h : QShape4 Kt) {m : ℕ}
    (hm : SmallOrder3 m) : ¬ Nat.card Kt ∣ m := by
  intro hdvd
  obtain ⟨f, hf⟩ := h
  obtain ⟨k, hk, hcard⟩ := card_of_lieModel_twistedG2 hf
  rw [hcard] at hdvd
  exact hm.not_pow_dvd (p := 3) (e := 9) Nat.prime_three (by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) ((three_pow_nine_dvd_ordRee k hk).trans hdvd)

theorem not_dvd_of_qShapeNS_three {Kt : Type} [Group Kt] (h : QShapeNS Kt) {m : ℕ}
    (hm : SmallOrder3 m) (hm0 : 0 < m) (hj : NotJ1Order m) : ¬ Nat.card Kt ∣ m := by
  rcases h with h | h | h | h
  · exact not_dvd_of_qShape1_three h hm hm0
  · exact not_dvd_of_qShape3_three h hm hm0
  · exact not_dvd_of_qShape4_three h hm
  · exact CFSG.GH74.Generic.BProg.B2.ShapeOrders.not_dvd_of_qShape5 h hj

theorem false_of_card_three {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) {m : ℕ} (hm : Nat.card ↥H = m) (hsm : SmallOrder3 m)
    (hm0 : 0 < m) (hj : NotJ1Order m) : False := by
  obtain ⟨Kt, _, hQ, hdvd⟩ := hs.exists_shape_card_dvd (m := m)
    (hm ▸ Subgroup.card_dvd_of_le inf_le_left)
  exact not_dvd_of_qShapeNS_three hQ hsm hm0 hj hdvd

theorem pumpup_l3three : PumpupEmpty (fun X _ => LieModel X .PSL 3 3 1) := by
  intro N _ _ H t L hs hS
  have hc := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hS
  exact false_of_card_three hs (m := 5616) (hc.trans (by decide))
    (smallOrder3_of_dvd (m := 5616) (by decide) (by decide) (by decide) (by decide)) (by decide)
    (notJ1Order_of_not_dvd (m := 5616) (by decide))

theorem pumpup_u3three : PumpupEmpty (fun X _ => LieModel X .PSU 3 3 1) := by
  intro N _ _ H t L hs hS
  have hc := CFSG.GH74.card_of_lieModel_PSU (n := 3) (by norm_num) (by norm_num) hS
  exact false_of_card_three hs (m := 6048) (hc.trans (by decide))
    (smallOrder3_of_dvd (m := 6048) (by decide) (by decide) (by decide) (by decide)) (by decide)
    (notJ1Order_of_not_dvd (m := 6048) (by decide))

theorem pumpup_l4three : PumpupEmpty (fun X _ => LieModel X .PSL 4 3 1) := by
  intro N _ _ H t L hs hS
  have hc := CFSG.GH74.card_of_lieModel_PSL (n := 4) (by norm_num) hS
  exact false_of_card_three hs (m := 6065280) (hc.trans (by decide))
    (smallOrder3_of_dvd (m := 6065280) (by decide) (by decide) (by decide) (by decide)) (by decide)
    (notJ1Order_of_not_dvd (m := 6065280) (by decide))

theorem pumpup_u4three : PumpupEmpty (fun X _ => LieModel X .PSU 4 3 1) := by
  intro N _ _ H t L hs hS
  have hc := CFSG.GH74.card_of_lieModel_PSU (n := 4) (by norm_num) (by norm_num) hS
  exact false_of_card_three hs (m := 3265920) (hc.trans (by decide))
    (smallOrder3_of_dvd (m := 3265920) (by decide) (by decide) (by decide) (by decide)) (by decide)
    (notJ1Order_of_not_dvd (m := 3265920) (by decide))

theorem pumpup_g2three : PumpupEmpty (fun X _ => LieModel X .G2 0 3 1) := by
  intro N _ _ H t L hs hS
  have hc := CFSG.GH74.card_of_lieModel_G2 (n := 0) (p := 3) (by norm_num) hS
  exact false_of_card_three hs (m := 4245696) (hc.trans (by decide))
    (smallOrder3_of_dvd (m := 4245696) (by decide) (by decide) (by decide) (by decide)) (by decide)
    (notJ1Order_of_not_dvd (m := 4245696) (by decide))

end Certified

end CFSG.GH74.Generic.BProg.B2.PumpupTableThree
