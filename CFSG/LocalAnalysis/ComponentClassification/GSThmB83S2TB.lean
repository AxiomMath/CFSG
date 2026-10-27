module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.GH74.GLS.Stage2.Final.ModelArith
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Sp4TB

theorem coprime_pow_sub_one {Q : ℕ} (hQ : 1 ≤ Q) (k : ℕ) (hk : 1 ≤ k) :
    Nat.Coprime Q (Q ^ k - 1) := by
  have h1 : Q ^ k - 1 + 1 = Q ^ k := Nat.sub_add_cancel (Nat.one_le_pow _ _ hQ)
  have h2 : Nat.Coprime (Q ^ k - 1) (Q ^ k - 1 + 1) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  rw [h1] at h2
  exact (h2.coprime_dvd_right (dvd_pow_self Q (by omega))).symm

theorem lt_of_le_sq {Q Q' : ℕ} (hQ : 5 ≤ Q) (hQ' : Q' ≤ (Q + 1) ^ 2) :
    Q' * (Q' ^ 2 - 1) < Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) := by
  have h4 : 625 ≤ Q ^ 4 :=
    calc 625 = 5 ^ 4 := by norm_num
      _ ≤ Q ^ 4 := Nat.pow_le_pow_left hQ 4
  have hA : Q ^ 2 ≤ 2 * (Q ^ 2 - 1) := by
    have : 25 ≤ Q ^ 2 := by nlinarith
    omega
  have hB : Q ^ 4 ≤ 2 * (Q ^ 4 - 1) := by omega
  have h1 : Q' * (Q' ^ 2 - 1) ≤ Q' ^ 3 :=
    calc Q' * (Q' ^ 2 - 1) ≤ Q' * Q' ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = Q' ^ 3 := by ring
  have h2 : Q' ^ 3 ≤ (Q + 1) ^ 6 :=
    calc Q' ^ 3 ≤ ((Q + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hQ' 3
      _ = (Q + 1) ^ 6 := by ring
  have h3 : (Q + 1) ^ 6 ≤ 64 * Q ^ 6 :=
    calc (Q + 1) ^ 6 ≤ (2 * Q) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      _ = 64 * Q ^ 6 := by ring
  have h5 : 256 * Q ^ 6 < Q ^ 10 := by
    have hQ6 : 0 < Q ^ 6 := by positivity
    calc 256 * Q ^ 6 < Q ^ 4 * Q ^ 6 := by nlinarith
      _ = Q ^ 10 := by ring
  have h6 : Q ^ 10 ≤ 4 * (Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1))) :=
    calc Q ^ 10 = Q ^ 4 * (Q ^ 2 * Q ^ 4) := by ring
      _ ≤ Q ^ 4 * ((2 * (Q ^ 2 - 1)) * (2 * (Q ^ 4 - 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hA hB)
      _ = 4 * (Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1))) := by ring
  omega

theorem le_sq_of_dvd {R p' f' : ℕ} (hp' : p'.Prime) (hp2' : p' ≠ 2) (hf' : 1 ≤ f')
    (hd : p' ^ f' ∣ (R * (R + 2)) * (R * (R + 2) * ((R + 1) ^ 2 + 1))) (hR : 1 ≤ R) :
    p' ^ f' ≤ (R + 2) ^ 2 := by
  have n2 := GH74.GLS.Stage2.Final.ModelArith.not_dvd_two hp' hp2'
  have hM : (R * (R + 2)) * (R * (R + 2) * ((R + 1) ^ 2 + 1)) =
      R ^ 2 * ((R + 2) ^ 2 * ((R + 1) ^ 2 + 1)) := by ring
  rw [hM] at hd
  have hpd : p' ∣ R ^ 2 * ((R + 2) ^ 2 * ((R + 1) ^ 2 + 1)) :=
    (dvd_pow_self p' (by omega)).trans hd
  have hC : (R + 1) ^ 2 + 1 = R * (R + 2) + 2 := by ring
  rcases (Nat.Prime.dvd_mul hp').mp hpd with h1 | h1
  ·
    have hR' : p' ∣ R := hp'.dvd_of_dvd_pow h1
    have c2 : Nat.Coprime p' (R + 2) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp']
      exact fun h2 => n2 ((Nat.dvd_add_right hR').mp h2)
    have c3 : Nat.Coprime p' ((R + 1) ^ 2 + 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp', hC]
      exact fun h3 => n2 ((Nat.dvd_add_right (dvd_mul_of_dvd_left hR' _)).mp h3)
    have c : Nat.Coprime (p' ^ f') ((R + 2) ^ 2 * ((R + 1) ^ 2 + 1)) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.mul_right (c2.pow_right 2) c3)
    have := Nat.le_of_dvd (by positivity) (c.dvd_of_dvd_mul_right hd)
    nlinarith
  · rcases (Nat.Prime.dvd_mul hp').mp h1 with h2 | h2
    ·
      have hR2 : p' ∣ R + 2 := hp'.dvd_of_dvd_pow h2
      have c1 : Nat.Coprime p' R := by
        rw [Nat.Prime.coprime_iff_not_dvd hp']
        exact fun h0 => n2 ((Nat.dvd_add_right h0).mp hR2)
      have c3 : Nat.Coprime p' ((R + 1) ^ 2 + 1) := by
        rw [Nat.Prime.coprime_iff_not_dvd hp', hC]
        exact fun h3 => n2 ((Nat.dvd_add_right (dvd_mul_of_dvd_right hR2 _)).mp h3)
      have hd' : p' ^ f' ∣ (R + 2) ^ 2 * (R ^ 2 * ((R + 1) ^ 2 + 1)) := by
        have e : R ^ 2 * ((R + 2) ^ 2 * ((R + 1) ^ 2 + 1)) =
            (R + 2) ^ 2 * (R ^ 2 * ((R + 1) ^ 2 + 1)) := by ring
        rwa [e] at hd
      have c : Nat.Coprime (p' ^ f') (R ^ 2 * ((R + 1) ^ 2 + 1)) :=
        Nat.Coprime.pow_left _ (Nat.Coprime.mul_right (c1.pow_right 2) c3)
      exact Nat.le_of_dvd (by positivity) (c.dvd_of_dvd_mul_right hd')
    ·
      have c1 : Nat.Coprime p' R := by
        rw [Nat.Prime.coprime_iff_not_dvd hp']
        intro h0
        rw [hC] at h2
        exact n2 ((Nat.dvd_add_right (dvd_mul_of_dvd_left h0 _)).mp h2)
      have c2 : Nat.Coprime p' (R + 2) := by
        rw [Nat.Prime.coprime_iff_not_dvd hp']
        intro h0
        rw [hC] at h2
        exact n2 ((Nat.dvd_add_right (dvd_mul_of_dvd_right h0 _)).mp h2)
      have hd' : p' ^ f' ∣ ((R + 1) ^ 2 + 1) * (R ^ 2 * (R + 2) ^ 2) := by
        have e : R ^ 2 * ((R + 2) ^ 2 * ((R + 1) ^ 2 + 1)) =
            ((R + 1) ^ 2 + 1) * (R ^ 2 * (R + 2) ^ 2) := by ring
        rwa [e] at hd
      have c : Nat.Coprime (p' ^ f') (R ^ 2 * (R + 2) ^ 2) :=
        Nat.Coprime.pow_left _ (Nat.Coprime.mul_right (c1.pow_right 2) (c2.pow_right 2))
      have := Nat.le_of_dvd (by positivity) (c.dvd_of_dvd_mul_right hd')
      nlinarith

theorem ne_of_prime_pow {p f p' f' : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hp' : p'.Prime) (hp2' : p' ≠ 2) (hf' : 1 ≤ f') :
    p' ^ f' * ((p' ^ f') ^ 2 - 1) ≠ (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := by
  intro hE
  have hQ1 : 1 ≤ p ^ f := by omega
  have hQ'1 : 1 ≤ p' ^ f' := Nat.one_le_pow _ _ hp'.pos
  have hpQ : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hpQ' : p' ∣ p' ^ f' := dvd_pow_self p' (by omega)
  by_cases hpp : p' = p
  · subst hpp
    have cM : Nat.Coprime p' (((p' ^ f) ^ 2 - 1) * ((p' ^ f) ^ 4 - 1)) :=
      Nat.Coprime.mul_right ((coprime_pow_sub_one hQ1 2 (by norm_num)).coprime_dvd_left hpQ)
        ((coprime_pow_sub_one hQ1 4 (by norm_num)).coprime_dvd_left hpQ)
    have cN : Nat.Coprime p' ((p' ^ f') ^ 2 - 1) :=
      (coprime_pow_sub_one hQ'1 2 (by norm_num)).coprime_dvd_left hpQ'
    have h1 : p' ^ f' ∣ (p' ^ f) ^ 4 := by
      have : p' ^ f' ∣ (p' ^ f) ^ 4 * (((p' ^ f) ^ 2 - 1) * ((p' ^ f) ^ 4 - 1)) :=
        hE ▸ dvd_mul_right _ _
      exact (cM.pow_left f').dvd_of_dvd_mul_right this
    have h2 : (p' ^ f) ^ 4 ∣ p' ^ f' := by
      have : (p' ^ f) ^ 4 ∣ p' ^ f' * ((p' ^ f') ^ 2 - 1) := hE ▸ dvd_mul_right _ _
      have c4 : Nat.Coprime ((p' ^ f) ^ 4) ((p' ^ f') ^ 2 - 1) := by
        rw [← pow_mul]
        exact cN.pow_left _
      exact c4.dvd_of_dvd_mul_right this
    have heq : p' ^ f' = (p' ^ f) ^ 4 := Nat.dvd_antisymm h1 h2
    rw [heq] at hE
    have hE' := Nat.eq_of_mul_eq_mul_left (by positivity) hE
    set Q := p' ^ f
    have hle : (Q ^ 2 - 1) * (Q ^ 4 - 1) ≤ Q ^ 6 :=
      calc (Q ^ 2 - 1) * (Q ^ 4 - 1) ≤ Q ^ 2 * Q ^ 4 :=
            Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
        _ = Q ^ 6 := by ring
    have hlt : Q ^ 6 < (Q ^ 4) ^ 2 - 1 := by
      have h8 : (Q ^ 4) ^ 2 = Q ^ 6 * Q ^ 2 := by ring
      have hQ2 : 25 ≤ Q ^ 2 := by nlinarith
      have hQ6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
      have : Q ^ 6 * 25 ≤ Q ^ 6 * Q ^ 2 := Nat.mul_le_mul_left _ hQ2
      rw [h8]
      omega
    omega
  · have c : Nat.Coprime (p' ^ f') ((p ^ f) ^ 4) := by
      rw [← pow_mul]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' hp).mpr hpp)
    have hd : p' ^ f' ∣ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) := by
      have : p' ^ f' ∣ (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) :=
        hE ▸ dvd_mul_right _ _
      exact c.dvd_of_dvd_mul_left this
    obtain ⟨R, hR⟩ : ∃ R, p ^ f = R + 1 := ⟨p ^ f - 1, by omega⟩
    have e2 : (p ^ f) ^ 2 - 1 = R * (R + 2) := by
      rw [hR]
      have : (R + 1) ^ 2 = R * (R + 2) + 1 := by ring
      omega
    have e4 : (p ^ f) ^ 4 - 1 = R * (R + 2) * ((R + 1) ^ 2 + 1) := by
      rw [hR]
      have : (R + 1) ^ 4 = R * (R + 2) * ((R + 1) ^ 2 + 1) + 1 := by ring
      omega
    rw [e2, e4] at hd
    have hle : p' ^ f' ≤ (p ^ f + 1) ^ 2 := by
      rw [hR]
      exact le_sq_of_dvd hp' hp2' hf' hd (by omega)
    have hlt := lt_of_le_sq h5 hle
    omega

theorem le_two_mul_ordBC {Q : ℕ} (hQ : 5 ≤ Q) :
    9360000 ≤ Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) := by
  have h2 : 25 ≤ Q ^ 2 :=
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
  have h4 : 625 ≤ Q ^ 4 :=
    calc 625 = 5 ^ 4 := by norm_num
      _ ≤ Q ^ 4 := Nat.pow_le_pow_left hQ 4
  calc 9360000 = 625 * (24 * 624) := by norm_num
    _ ≤ Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) :=
        Nat.mul_le_mul h4 (Nat.mul_le_mul (by omega) (by omega))

theorem ne_two_mul_card_He {Q : ℕ} (hQ : 5 ≤ Q) :
    Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) ≠ 2 * 4030387200 := by
  intro h
  rcases Nat.lt_or_ge Q 11 with hlt | hge
  · interval_cases Q <;> norm_num at h
  · have h2 : 121 ≤ Q ^ 2 :=
      calc 121 = 11 ^ 2 := by norm_num
        _ ≤ Q ^ 2 := Nat.pow_le_pow_left hge 2
    have h4 : 14641 ≤ Q ^ 4 :=
      calc 14641 = 11 ^ 4 := by norm_num
        _ ≤ Q ^ 4 := Nat.pow_le_pow_left hge 4
    have : 14641 * (120 * 14640) ≤ Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) :=
      Nat.mul_le_mul h4 (Nat.mul_le_mul (by omega) (by omega))
    omega

theorem two_mul_ordA_one {q : ℕ} (hq : Odd q) : 2 * Open.ordA 1 q = q * (q ^ 2 - 1) := by
  have hg : Nat.gcd (1 + 1) (q - 1) = 2 := by
    obtain ⟨k, rfl⟩ := hq
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  have hev : 2 ∣ q * (q ^ 2 - 1) :=
    (even_iff_two_dvd.1 (Nat.Odd.sub_odd hq.pow odd_one)).mul_left _
  unfold Open.ordA
  rw [hg, show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  exact Nat.mul_div_cancel' hev

theorem two_mul_card_psp {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Blueprint.LieModel Y .PSp 2 p f) :
    2 * Nat.card Y = (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := by
  rw [(ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).2.2.1 rfl]
  exact GH74.GLS.Stage2.Final.ModelArith.two_mul_ordBC_two (hp.odd_of_ne_two hp2).pow

theorem two_mul_card_psl_two {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Blueprint.LieModel Y .PSL 2 p f) : 2 * Nat.card Y = p ^ f * ((p ^ f) ^ 2 - 1) := by
  rw [(ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).1 rfl]
  exact two_mul_ordA_one (hp.odd_of_ne_two hp2).pow

theorem card_psl_three_four {Y : Type} [Group Y] (h : Blueprint.LieModel Y .PSL 3 2 2) :
    Nat.card Y = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four (h.statedClassicalModel (by decide))

theorem false_of_unbalancingTriple_psp
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {w a : X} {L : Subgroup X} (hT : GSUnbalancingTriple w a L)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hL : Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSp 2 p f)
    (hZ : center (L ⧸ pPrimeCore 2 L) = ⊥) : False := by
  have hc := two_mul_card_psp hp hp2 hL
  have hlow := le_two_mul_ordBC h5
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun hf0 => by rw [hf0, pow_zero] at h5; omega
  rcases hTB X hnonab hK hz hU w a L hT with ⟨n, hn, h9, he⟩ |
      (h7 | ⟨p', f', hp', hp2', hf', -, hL'⟩) | (hHe | hL34)
  · exact hSA X hnonab hK hz hU ⟨w, L, n, hT.1, hn, h9, hT.2.2.2.1, hT.2.2.2.2.1, he⟩
  · obtain ⟨e⟩ := h7
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_seven] at hc
    omega
  · exact ne_of_prime_pow hp hf h5 hp' hp2' hf'
      ((two_mul_card_psl_two hp' hp2' hL').symm.trans hc)
  · obtain ⟨e⟩ := hHe
    rw [Nat.card_congr e.toEquiv, Sporadic.He.card_He] at hc
    exact ne_two_mul_card_He h5 hc.symm
  · have h1 : Nat.card (L ⧸ pPrimeCore 2 L) = 20160 :=
      (card_zStarBar_of_center_eq_bot hZ).symm.trans (card_psl_three_four hL34)
    rw [h1] at hc
    omega

end Sp4TB

end CFSG.ComponentClassification.GSThmB
