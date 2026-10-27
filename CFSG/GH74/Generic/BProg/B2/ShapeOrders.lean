module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Orders.LieType
public import CFSG.Sporadic.J1

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.Open (ordA ordTwistedA ordRee)

namespace ShapeOrders

theorem prime_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p = 3 ∨ p = 5 ∨ 7 ≤ p := by
  have h2 := hp.two_le
  by_contra hc
  simp only [not_or, not_le] at hc
  obtain ⟨h3, h5, h7⟩ := hc
  interval_cases p
  · exact absurd rfl hp2
  · exact h3 rfl
  · exact absurd hp (by decide)
  · exact h5 rfl
  · exact absurd hp (by decide)

theorem prod_Icc_two_three {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 2 3, f i = f 2 * f 3 := by
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]

theorem prod_Icc_two_four {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 2 4, f i = f 2 * f 3 * f 4 := by
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide]
  simp [Finset.prod_insert, mul_assoc]

theorem exists_prime_pow_card (F : Type) [Field F] [Finite F] :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ Nat.card F = p ^ f := by
  have := Fintype.ofFinite F
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  obtain ⟨n, hn, hcard⟩ := FiniteField.card F p
  exact ⟨p, n, hn, n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

theorem card_statedSL4 {F : Type} [Field F] [Finite F] :
    Nat.card (StatedSL 4 F) =
      Nat.card F ^ 6 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 4 - 1)) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 4 F).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num : 1 ≤ 4),
    show Finset.Icc 2 4 = {2, 3, 4} by decide]
  simp [Finset.prod_insert, mul_assoc]

theorem toNat_pow_sub_neg_one_pow (q i : ℕ) (hq : 1 ≤ q) (hi : Even i) :
    (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat = q ^ i - 1 := by
  have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  rw [hi.neg_one_pow]
  have : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub h1]; push_cast; ring
  rw [this, Int.toNat_natCast]

theorem pow_six_dvd_psu4 (q : ℕ) (hq : 1 ≤ q) :
    q ^ 6 ∣ q ^ (4 * (4 - 1) / 2) * ((((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat *
      (((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat * (((q : ℕ) : ℤ) ^ 4 - (-1) ^ 4).toNat) /
        Nat.gcd 4 (q + 1) := by
  have h2 := toNat_pow_sub_neg_one_pow q 2 hq (by decide)
  have hg : Nat.gcd 4 (q + 1) ∣ (((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat *
      (((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat * (((q : ℕ) : ℤ) ^ 4 - (-1) ^ 4).toNat := by
    have h1 : Nat.gcd 4 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
    have h3 : q + 1 ∣ q ^ 2 - 1 := by
      have := Nat.sq_sub_sq q 1
      rw [one_pow] at this
      rw [this]
      exact Dvd.intro _ rfl
    rw [h2]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (h1.trans h3) _) _
  rw [Nat.mul_div_assoc _ hg, show 4 * (4 - 1) / 2 = 6 by norm_num]
  exact Dvd.intro _ rfl

theorem pow_three_dvd_ordA (q : ℕ) : q ^ 3 ∣ ordA 2 q := by
  unfold ordA
  rw [prod_Icc_two_three]
  have hg : Nat.gcd (2 + 1) (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    have h1 : Nat.gcd (2 + 1) (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2 : q - 1 ∣ q ^ 3 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow q 1 3
    exact Dvd.dvd.mul_left (h1.trans h2) _
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.intro _ rfl

theorem pow_three_dvd_ordTwistedA (q : ℕ) : q ^ 3 ∣ ordTwistedA 2 q := by
  unfold ordTwistedA
  rw [prod_Icc_two_three]
  have hg : Nat.gcd (2 + 1) (q + 1) ∣
      ((q ^ 2 - (-1 : ℤ) ^ 2).toNat * (q ^ 3 - (-1 : ℤ) ^ 3).toNat) := by
    have h1 : Nat.gcd (2 + 1) (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
    have h2 : q + 1 ∣ (q ^ 3 - (-1 : ℤ) ^ 3).toNat := by
      have : (q ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
        have : (q : ℤ) ^ 3 - (-1) ^ 3 = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [this, Int.toNat_natCast]
      rw [this]
      simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
    exact Dvd.dvd.mul_left (h1.trans h2) _
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.intro _ rfl

theorem three_pow_nine_dvd_ordRee (k : ℕ) (hk : 1 ≤ k) : 3 ^ 9 ∣ ordRee (3 ^ (2 * k + 1)) := by
  unfold ordRee
  have h : 3 ^ 9 ∣ (3 ^ (2 * k + 1)) ^ 3 := by
    rw [← pow_mul]
    exact pow_dvd_pow 3 (by omega)
  exact h.trans (((dvd_refl _).mul_right _).mul_right _)

@[expose] def SmallOrder (m : ℕ) : Prop :=
  ¬ 3 ^ 6 ∣ m ∧ ¬ 5 ^ 3 ∣ m ∧ ∀ p : ℕ, p.Prime → 7 ≤ p → ¬ p ^ 2 ∣ m

@[expose] def NotJ1Order (m : ℕ) : Prop := ¬ (7 ∣ m ∧ 19 ∣ m)

theorem SmallOrder.of_dvd {m M : ℕ} (hM : SmallOrder M) (h : m ∣ M) : SmallOrder m :=
  ⟨fun h1 => hM.1 (h1.trans h), fun h1 => hM.2.1 (h1.trans h),
    fun p hp hp7 h1 => hM.2.2 p hp hp7 (h1.trans h)⟩

theorem NotJ1Order.of_dvd {m M : ℕ} (hM : NotJ1Order M) (h : m ∣ M) : NotJ1Order m :=
  fun h1 => hM ⟨h1.1.trans h, h1.2.trans h⟩

theorem smallOrder_M0 : SmallOrder (2 ^ 10 * 3 ^ 5 * 5 ^ 2 * 7 * 11 * 17 * 19 * 23) := by
  refine ⟨by decide, by decide, fun p hp hp7 h => ?_⟩
  have h1 : p ∣ 2 ^ 10 * 3 ^ 5 * 5 ^ 2 * 7 * 11 * 17 * 19 * 23 :=
    (dvd_pow_self p two_ne_zero).trans h
  have hpr : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  simp only [hp.dvd_mul] at h1
  rcases h1 with ((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1
  · have := hpr 2 Nat.prime_two (hp.dvd_of_dvd_pow h1); omega
  · have := hpr 3 Nat.prime_three (hp.dvd_of_dvd_pow h1); omega
  · have := hpr 5 Nat.prime_five (hp.dvd_of_dvd_pow h1); omega
  · have := hpr 7 (by norm_num) h1; subst this; revert h; decide
  · have := hpr 11 (by norm_num) h1; subst this; revert h; decide
  · have := hpr 17 (by norm_num) h1; subst this; revert h; decide
  · have := hpr 19 (by norm_num) h1; subst this; revert h; decide
  · have := hpr 23 (by norm_num) h1; subst this; revert h; decide

theorem smallOrder_of_dvd_M0 {m : ℕ} (h : m ∣ 2 ^ 10 * 3 ^ 5 * 5 ^ 2 * 7 * 11 * 17 * 19 * 23) :
    SmallOrder m :=
  smallOrder_M0.of_dvd h

theorem SmallOrder.not_pow_dvd {m : ℕ} (hm : SmallOrder m) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : p = 3 → 6 ≤ e) (h5 : p = 5 → 3 ≤ e) (h7 : 7 ≤ p → 2 ≤ e) : ¬ p ^ e ∣ m := by
  intro h
  rcases prime_cases hp hp2 with rfl | rfl | h7'
  · exact hm.1 ((pow_dvd_pow 3 (h3 rfl)).trans h)
  · exact hm.2.1 ((pow_dvd_pow 5 (h5 rfl)).trans h)
  · exact hm.2.2 p hp h7' ((pow_dvd_pow p (h7 h7')).trans h)

theorem qShape1_facts {Kt : Type} [Group Kt] (h : QShape1 Kt) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ (6 * f) ∣ Nat.card Kt := by
  rcases h with ⟨F, hF, hFin, hmod, ⟨e⟩⟩ | ⟨q, F, hF, hFin, hcard, hq4, ⟨e⟩⟩
  · obtain ⟨p, f, hp, hf, hcardF⟩ := exists_prime_pow_card F
    have hKt : Nat.card Kt = Nat.card (StatedSL 4 F) := Nat.card_congr e.toEquiv
    rw [card_statedSL4, hcardF] at hKt
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      rw [hcardF] at hmod
      omega
    refine ⟨p, f, hp, hp2, hf, ?_⟩
    rw [hKt, mul_comm 6 f, pow_mul]
    exact Dvd.intro _ rfl
  · obtain ⟨p, f, hpp, hchar, rfl⟩ := L5U5.exists_prime_pow_of_card_eq_sq hcard
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
    have hdvd : Nat.card (StatedProj (StatedSU 4 (p ^ f) F)) ∣ Nat.card (StatedSU 4 (p ^ f) F) :=
      Subgroup.card_quotient_dvd_card _
    have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (n := 4) hpp' hf hcard
      (by norm_num)
    rw [prod_Icc_two_four] at h1
    refine ⟨p, f, hpp', hp2, hf, ?_⟩
    rw [hKt, mul_comm 6 f, pow_mul]
    refine Dvd.dvd.trans ?_ hdvd
    rw [h1]
    exact pow_six_dvd_psu4 (p ^ f) (Nat.one_le_pow _ _ hpp'.pos)

theorem qShape3_facts {Kt : Type} [Group Kt] (h : QShape3 Kt) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 < p ^ f ∧ p ^ (3 * f) ∣ Nat.card Kt := by
  obtain ⟨p, f, hp, hp2, hq, h⟩ := h
  have hf : 1 ≤ f := by
    by_contra hf0
    have : f = 0 := by omega
    subst this
    simp at hq
  refine ⟨p, f, hp, hp2, hf, hq, ?_⟩
  rw [mul_comm 3 f, pow_mul]
  rcases h with h | h
  · rw [card_of_lieModel_PSL (by norm_num) h]
    exact pow_three_dvd_ordA (p ^ f)
  · rw [card_of_lieModel_PSU (by norm_num) hp2 h]
    exact pow_three_dvd_ordTwistedA (p ^ f)

theorem qShape5_facts {Kt : Type} [Group Kt] (h : QShape5 Kt) :
    Nat.card Kt = 175560 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.J1.card_J1

theorem not_dvd_of_qShape13 {Kt : Type} [Group Kt] (h : QShape1 Kt ∨ QShape3 Kt) {m : ℕ}
    (hm : SmallOrder m) : ¬ Nat.card Kt ∣ m := by
  intro hdvd
  rcases h with h | h
  · obtain ⟨p, f, hp, hp2, hf, hpf⟩ := qShape1_facts h
    exact hm.not_pow_dvd hp hp2 (fun _ => by omega) (fun _ => by omega) (fun _ => by omega)
      (hpf.trans hdvd)
  · obtain ⟨p, f, hp, hp2, hf, hq, hpf⟩ := qShape3_facts h
    refine hm.not_pow_dvd hp hp2 (fun h3 => ?_) (fun _ => by omega) (fun _ => by omega)
      (hpf.trans hdvd)
    subst h3
    by_contra hlt
    have : f = 1 := by omega
    subst this
    simp at hq

theorem not_dvd_of_qShape5 {Kt : Type} [Group Kt] (h : QShape5 Kt)
    {m : ℕ} (hm : NotJ1Order m) : ¬ Nat.card Kt ∣ m := by
  intro hdvd
  rw [qShape5_facts h] at hdvd
  exact hm ⟨(by norm_num : 7 ∣ 175560).trans hdvd, (by norm_num : 19 ∣ 175560).trans hdvd⟩

section Certified

theorem not_dvd_of_qShape4 {Kt : Type} [Group Kt] (h : QShape4 Kt) {m : ℕ} (hm : SmallOrder m) :
    ¬ Nat.card Kt ∣ m := by
  intro hdvd
  obtain ⟨f, hf⟩ := h
  obtain ⟨k, hk, hcard⟩ := card_of_lieModel_twistedG2 hf
  rw [hcard] at hdvd
  exact hm.not_pow_dvd (p := 3) (e := 9) Nat.prime_three (by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) ((three_pow_nine_dvd_ordRee k hk).trans hdvd)

theorem not_dvd_of_qShapeNS {Kt : Type} [Group Kt] (h : QShapeNS Kt) {m : ℕ} (hm : SmallOrder m)
    (hj : NotJ1Order m) : ¬ Nat.card Kt ∣ m := by
  rcases h with h | h | h | h
  · exact not_dvd_of_qShape13 (Or.inl h) hm
  · exact not_dvd_of_qShape13 (Or.inr h) hm
  · exact not_dvd_of_qShape4 h hm
  · exact not_dvd_of_qShape5 h hj

theorem not_dvd_alt_of_shape {Kt : Type} [Group Kt] (h : QShapeNS Kt) (n : ℕ) (hn : n ≤ 11) :
    ¬ Nat.card Kt ∣ Nat.card (alternatingGroup (Fin n)) := by
  have h1 : Nat.card (alternatingGroup (Fin n)) ∣ Nat.card (Equiv.Perm (Fin n)) :=
    Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have h3 : Nat.card (alternatingGroup (Fin n)) ∣ Nat.factorial 11 :=
    (h2 ▸ h1).trans (Nat.factorial_dvd_factorial hn)
  have h4 : Nat.factorial 11 ∣ 2 ^ 10 * 3 ^ 5 * 5 ^ 2 * 7 * 11 * 17 * 19 * 23 := by decide
  have h5 : NotJ1Order (Nat.factorial 11) := fun h => absurd h.2 (by decide)
  exact not_dvd_of_qShapeNS h (smallOrder_of_dvd_M0 (h3.trans h4)) (h5.of_dvd h3)

end Certified

end ShapeOrders

theorem ShapeInCent.exists_shape_card_dvd {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) {m : ℕ}
    (hm : Nat.card ↥(H ⊓ centralizer ({t} : Set N)) ∣ m) :
    ∃ (Kt : Type) (_ : Group Kt), QShapeNS Kt ∧ Nat.card Kt ∣ m := by
  obtain ⟨Z, -, -, hZn, hQ⟩ := h.shape
  exact ⟨↥L ⧸ Z, QuotientGroup.Quotient.group Z, hQ,
    (Subgroup.card_quotient_dvd_card Z).trans
      ((Subgroup.card_dvd_of_le h.comp.1).trans hm)⟩

section Certified

theorem not_alt_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (h : ShapeInCent H t L) (n : ℕ) (hn : n ≤ 11) :
    ¬ Nonempty (↥H ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  obtain ⟨Kt, _, hQ, hdvd⟩ := h.exists_shape_card_dvd
    (m := Nat.card (alternatingGroup (Fin n)))
    ((Subgroup.card_dvd_of_le inf_le_left).trans (Nat.card_congr e.toEquiv).dvd)
  exact ShapeOrders.not_dvd_alt_of_shape hQ n hn hdvd

end Certified

end CFSG.GH74.Generic.BProg.B2
