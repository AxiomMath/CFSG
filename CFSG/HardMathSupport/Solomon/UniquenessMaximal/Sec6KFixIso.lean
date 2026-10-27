module

public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KFixModel
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
import CFSG.Timmesfeld.Orders.ClassicalLinearThree

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs


theorem kfix_bnd_a {p ℓ a b g : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (ha : 1 ≤ a)
    (hpl : p ≠ ℓ) (hg : Nat.Coprime (ℓ ^ b) g)
    (hd : (ℓ ^ b) ^ 3 ∣ g * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1)))) :
    (ℓ ^ b) ^ 3 ≤ 4 * (p ^ a + 2) ^ 2 := by
  have hcop : Nat.Coprime ((p ^ a) ^ 3) ((ℓ ^ b) ^ 3) :=
    Nat.Coprime.pow 3 3 (Nat.Coprime.pow a b ((Nat.coprime_primes hp hℓ).2 hpl))
  have hpa : 2 ≤ p ^ a := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  obtain ⟨x, hx⟩ : ∃ x, p ^ a = x + 1 := ⟨p ^ a - 1, by omega⟩
  have hc : Nat.Coprime ((ℓ ^ b) ^ 3) (g * (p ^ a) ^ 3) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_left 3 hg) hcop.symm
  have hE : (ℓ ^ b) ^ 3 ∣ ((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1) :=
    hc.dvd_of_dvd_mul_left (by rwa [← mul_assoc] at hd)
  rw [hx] at hE
  have e1 : (x + 1) ^ 2 - 1 = x * (x + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (x + 1) ^ 3 - 1 = x * (x ^ 2 + 3 * x + 3) := Nat.sub_eq_of_eq_add (by ring)
  have e : ((x + 1) ^ 2 - 1) * ((x + 1) ^ 3 - 1) = x ^ 2 * ((x + 2) * (x ^ 2 + 3 * x + 3)) := by
    rw [e1, e2]; ring
  rw [e] at hE
  have hx0 : 0 < x := by omega
  have := bndZ (ℓ := ℓ) (k := b * 3) (t := x) (a := x) (b := x + 2) hℓ hx0 (Or.inl ⟨rfl, rfl⟩)
    (by rw [pow_mul]; exact hE)
  calc (ℓ ^ b) ^ 3 = ℓ ^ (b * 3) := (pow_mul ℓ b 3).symm
    _ ≤ 4 * (x + 3) ^ 2 := this
    _ = 4 * (p ^ a + 2) ^ 2 := by rw [hx]

theorem kfix_bnd_b {p ℓ a b g : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hb : 1 ≤ b)
    (hpl : p ≠ ℓ) (hg : Nat.Coprime (p ^ a) g)
    (hd : (p ^ a) ^ 3 ∣ g * ((ℓ ^ b) ^ 3 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1)))) :
    (p ^ a) ^ 3 ≤ 4 * (ℓ ^ b + 1) ^ 2 := by
  have hcop : Nat.Coprime ((p ^ a) ^ 3) ((ℓ ^ b) ^ 3) :=
    Nat.Coprime.pow 3 3 (Nat.Coprime.pow a b ((Nat.coprime_primes hp hℓ).2 hpl))
  have hlb : 2 ≤ ℓ ^ b := by
    have := Nat.one_lt_pow (by omega : b ≠ 0) hℓ.one_lt
    omega
  obtain ⟨w, hw⟩ : ∃ w, ℓ ^ b = w + 2 := ⟨ℓ ^ b - 2, by omega⟩
  have hc : Nat.Coprime ((p ^ a) ^ 3) (g * (ℓ ^ b) ^ 3) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_left 3 hg) hcop
  have hF : (p ^ a) ^ 3 ∣ ((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1) :=
    hc.dvd_of_dvd_mul_left (by rwa [← mul_assoc] at hd)
  rw [hw] at hF
  have e1 : (w + 2) ^ 2 - 1 = (w + 1) * (w + 3) := Nat.sub_eq_of_eq_add (by ring)
  have e : ((w + 2) ^ 2 - 1) * ((w + 2) ^ 3 + 1) =
      (w + 3) ^ 2 * ((w + 1) * (w ^ 2 + 3 * w + 3)) := by
    rw [e1]; ring
  rw [e] at hF
  have := bndZ (ℓ := p) (k := a * 3) (t := w) (a := w + 3) (b := w + 1) hp (by omega)
    (Or.inr ⟨rfl, rfl⟩) (by rw [pow_mul]; exact hF)
  calc (p ^ a) ^ 3 = p ^ (a * 3) := (pow_mul p a 3).symm
    _ ≤ 4 * (w + 3) ^ 2 := this
    _ = 4 * (ℓ ^ b + 1) ^ 2 := by rw [hw]

theorem kfix_finite_check_l (q q' : ℕ) (hq : 2 ≤ q) (hq6 : q ≤ 6) (hq' : 2 ≤ q') (hq'6 : q' ≤ 6)
    (h : Nat.gcd 3 (q' - 1) * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) =
      Nat.gcd 3 (q - 1) * (q' ^ 3 * ((q' ^ 2 - 1) * (q' ^ 3 - 1)))) : q = q' := by
  interval_cases q <;> interval_cases q' <;> first | rfl | (exfalso; revert h; decide)

theorem kfix_finite_check_u (q q' : ℕ) (hq : 2 ≤ q) (hq6 : q ≤ 5) (hq' : 2 ≤ q') (hq'6 : q' ≤ 5)
    (h : Nat.gcd 3 (q' + 1) * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) =
      Nat.gcd 3 (q + 1) * (q' ^ 3 * ((q' ^ 2 - 1) * (q' ^ 3 + 1)))) : q = q' := by
  interval_cases q <;> interval_cases q' <;> first | rfl | (exfalso; revert h; decide)


theorem kfix_LL_inj {p ℓ a b : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : Nat.gcd 3 (ℓ ^ b - 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) =
      Nat.gcd 3 (p ^ a - 1) * ((ℓ ^ b) ^ 3 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 - 1)))) :
    p ^ a = ℓ ^ b := by
  have hpa : 2 ≤ p ^ a := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  have hlb : 2 ≤ ℓ ^ b := by
    have := Nat.one_lt_pow (by omega : b ≠ 0) hℓ.one_lt
    omega
  have hg1 : Nat.Coprime p (Nat.gcd 3 (p ^ a - 1)) :=
    coprime_of_not_dvd hp fun hh =>
      not_dvd_sub_one hp (by omega) (dvd_pow_self p (by omega))
        (hh.trans (Nat.gcd_dvd_right 3 _))
  have hg2 : Nat.Coprime ℓ (Nat.gcd 3 (ℓ ^ b - 1)) :=
    coprime_of_not_dvd hℓ fun hh =>
      not_dvd_sub_one hℓ (by omega) (dvd_pow_self ℓ (by omega))
        (hh.trans (Nat.gcd_dvd_right 3 _))
  by_cases hpl : p = ℓ
  · subst hpl
    have hE : Nat.Coprime p (Nat.gcd 3 (p ^ b - 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) :=
      Nat.Coprime.mul_right hg2
        (Nat.Coprime.mul_right (cop_pow_sub hp ha 2 (by norm_num))
          (cop_pow_sub hp ha 3 (by norm_num)))
    have hF : Nat.Coprime p (Nat.gcd 3 (p ^ a - 1) * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 - 1))) :=
      Nat.Coprime.mul_right hg1
        (Nat.Coprime.mul_right (cop_pow_sub hp hb 2 (by norm_num))
          (cop_pow_sub hp hb 3 (by norm_num)))
    have h1 : p ^ (a * 3) * (Nat.gcd 3 (p ^ b - 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) =
        p ^ (b * 3) * (Nat.gcd 3 (p ^ a - 1) * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 - 1))) := by
      calc _ = Nat.gcd 3 (p ^ b - 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) := by
            ring
        _ = Nat.gcd 3 (p ^ a - 1) * ((p ^ b) ^ 3 * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 - 1))) := h
        _ = _ := by ring
    have hexp : a = b := by
      have := exp_eq_of_mul_eq hp hE hF h1
      omega
    rw [hexp]
  · have hg2' : Nat.Coprime (ℓ ^ b) (Nat.gcd 3 (ℓ ^ b - 1)) := Nat.Coprime.pow_left b hg2
    have hg1' : Nat.Coprime (p ^ a) (Nat.gcd 3 (p ^ a - 1)) := Nat.Coprime.pow_left a hg1
    have h1 := kfix_bnd_a hp hℓ ha hpl hg2'
      ⟨Nat.gcd 3 (p ^ a - 1) * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 - 1)), by rw [h]; ring⟩
    have h2 := kfix_bnd_a hℓ hp hb (Ne.symm hpl) hg1'
      ⟨Nat.gcd 3 (ℓ ^ b - 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1)), by rw [← h]; ring⟩
    have h6 : p ^ a ≤ 6 ∧ ℓ ^ b ≤ 6 := by
      generalize p ^ a = q at *
      generalize ℓ ^ b = q' at *
      rcases le_total q q' with hle | hle
      · have : q' ≤ 6 := by
          by_contra hc
          have hc : 7 ≤ q' := by omega
          have h3 : (q + 2) ^ 2 ≤ (q' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have h7 : 7 * q' ^ 2 ≤ q' ^ 3 := by
            calc 7 * q' ^ 2 ≤ q' * q' ^ 2 := Nat.mul_le_mul_right _ hc
              _ = q' ^ 3 := by ring
          nlinarith
        omega
      · have : q ≤ 6 := by
          by_contra hc
          have hc : 7 ≤ q := by omega
          have h3 : (q' + 2) ^ 2 ≤ (q + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have h7 : 7 * q ^ 2 ≤ q ^ 3 := by
            calc 7 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hc
              _ = q ^ 3 := by ring
          nlinarith
        omega
    exact kfix_finite_check_l _ _ hpa h6.1 hlb h6.2 h

theorem kfix_UU_inj {p ℓ a b : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : Nat.gcd 3 (ℓ ^ b + 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1))) =
      Nat.gcd 3 (p ^ a + 1) * ((ℓ ^ b) ^ 3 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1)))) :
    p ^ a = ℓ ^ b := by
  have hpa : 2 ≤ p ^ a := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  have hlb : 2 ≤ ℓ ^ b := by
    have := Nat.one_lt_pow (by omega : b ≠ 0) hℓ.one_lt
    omega
  have hg1 : Nat.Coprime p (Nat.gcd 3 (p ^ a + 1)) :=
    coprime_of_not_dvd hp fun hh =>
      not_dvd_add_one hp (dvd_pow_self p (by omega)) (hh.trans (Nat.gcd_dvd_right 3 _))
  have hg2 : Nat.Coprime ℓ (Nat.gcd 3 (ℓ ^ b + 1)) :=
    coprime_of_not_dvd hℓ fun hh =>
      not_dvd_add_one hℓ (dvd_pow_self ℓ (by omega)) (hh.trans (Nat.gcd_dvd_right 3 _))
  by_cases hpl : p = ℓ
  · subst hpl
    have hE : Nat.Coprime p (Nat.gcd 3 (p ^ b + 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1))) :=
      Nat.Coprime.mul_right hg2
        (Nat.Coprime.mul_right (cop_pow_sub hp ha 2 (by norm_num))
          (cop_pow_add hp ha 3 (by norm_num)))
    have hF : Nat.Coprime p (Nat.gcd 3 (p ^ a + 1) * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 + 1))) :=
      Nat.Coprime.mul_right hg1
        (Nat.Coprime.mul_right (cop_pow_sub hp hb 2 (by norm_num))
          (cop_pow_add hp hb 3 (by norm_num)))
    have h1 : p ^ (a * 3) * (Nat.gcd 3 (p ^ b + 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1))) =
        p ^ (b * 3) * (Nat.gcd 3 (p ^ a + 1) * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 + 1))) := by
      calc _ = Nat.gcd 3 (p ^ b + 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1))) := by
            ring
        _ = Nat.gcd 3 (p ^ a + 1) * ((p ^ b) ^ 3 * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 + 1))) := h
        _ = _ := by ring
    have hexp : a = b := by
      have := exp_eq_of_mul_eq hp hE hF h1
      omega
    rw [hexp]
  · have hg2' : Nat.Coprime (ℓ ^ b) (Nat.gcd 3 (ℓ ^ b + 1)) := Nat.Coprime.pow_left b hg2
    have hg1' : Nat.Coprime (p ^ a) (Nat.gcd 3 (p ^ a + 1)) := Nat.Coprime.pow_left a hg1
    have h1 := kfix_bnd_b hℓ hp ha (Ne.symm hpl) hg2'
      ⟨Nat.gcd 3 (p ^ a + 1) * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1)), by rw [h]; ring⟩
    have h2 := kfix_bnd_b hp hℓ hb hpl hg1'
      ⟨Nat.gcd 3 (ℓ ^ b + 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)), by rw [← h]; ring⟩
    have h6 : p ^ a ≤ 5 ∧ ℓ ^ b ≤ 5 := by
      generalize p ^ a = q at *
      generalize ℓ ^ b = q' at *
      rcases le_total q q' with hle | hle
      · have : q' ≤ 5 := by
          by_contra hc
          have hc : 6 ≤ q' := by omega
          have h3 : (q + 1) ^ 2 ≤ (q' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have h7 : 6 * q' ^ 2 ≤ q' ^ 3 := by
            calc 6 * q' ^ 2 ≤ q' * q' ^ 2 := Nat.mul_le_mul_right _ hc
              _ = q' ^ 3 := by ring
          nlinarith
        omega
      · have : q ≤ 5 := by
          by_contra hc
          have hc : 6 ≤ q := by omega
          have h3 : (q' + 1) ^ 2 ≤ (q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have h7 : 6 * q ^ 2 ≤ q ^ 3 := by
            calc 6 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hc
              _ = q ^ 3 := by ring
          nlinarith
        omega
    exact kfix_finite_check_u _ _ hpa h6.1 hlb h6.2 h


theorem kfix_card_psl3_mul {K : Type} [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 3 K)) * Nat.gcd 3 (Nat.card K - 1) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
  CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd

theorem kfix_card_psu3_mul {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) :=
  CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd hp hf hK


theorem kfix_psl_data {Y : Type*} [Group Y] {r : ℕ} (h : IsPSLn 3 r Y) :
    ∃ p a : ℕ, p.Prime ∧ 1 ≤ a ∧ r = p ^ a ∧
      Nat.card Y * Nat.gcd 3 (r - 1) = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' F
  have hF : r = p ^ (n : ℕ) := by rw [← hc, Nat.card_eq_fintype_card]; exact hcard
  refine ⟨p, n, hp, n.pos, hF, ?_⟩
  have := kfix_card_psl3_mul (K := F)
  rw [hc] at this
  rw [Nat.card_congr e.toEquiv]
  exact this

theorem kfix_psu_data {Y : Type*} [Group Y] {r : ℕ} (h : IsPSUn 3 r Y) :
    ∃ p a : ℕ, p.Prime ∧ 1 ≤ a ∧ r = p ^ a ∧
      Nat.card Y * Nat.gcd 3 (r + 1) = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  have hr1 : r ≠ 1 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    rw [hc] at this
    simp at this
  obtain ⟨p, f, rfl, hK⟩ := kfix_exists_unitaryFieldData hc hr1
  exact ⟨p, f, hK.prime, hK.one_le, rfl, by
    rw [Nat.card_congr e.toEquiv]; exact kfix_card_psu3_mul hK.prime hK.one_le hc⟩


theorem inputL3iso_holds : InputL3iso := by
  intro Y _ r r' hr hr'
  have mixed : ∀ {s s' : ℕ}, IsPSLn 3 s Y → IsPSUn 3 s' Y → False := by
    intro s s' hs hs'
    obtain ⟨p, a, hp, ha, rfl, h1⟩ := kfix_psl_data hs
    obtain ⟨ℓ, b, hℓ, hb, rfl, h2⟩ := kfix_psu_data hs'
    apply CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith.order_psl3_ne_psu3 hp hℓ ha hb
    rw [← h1, ← h2]; ring
  refine ⟨?_, fun ⟨hl, hu⟩ => mixed hl hu⟩
  rcases hr with hl | hu <;> rcases hr' with hl' | hu'
  · obtain ⟨p, a, hp, ha, rfl, h1⟩ := kfix_psl_data hl
    obtain ⟨ℓ, b, hℓ, hb, rfl, h2⟩ := kfix_psl_data hl'
    exact kfix_LL_inj hp hℓ ha hb (by rw [← h1, ← h2]; ring)
  · exact (mixed hl hu').elim
  · exact (mixed hl' hu).elim
  · obtain ⟨p, a, hp, ha, rfl, h1⟩ := kfix_psu_data hu
    obtain ⟨ℓ, b, hℓ, hb, rfl, h2⟩ := kfix_psu_data hu'
    exact kfix_UU_inj hp hℓ ha hb (by rw [← h1, ← h2]; ring)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
