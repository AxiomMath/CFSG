module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open KFactsPair

theorem not_isUFourOdd_of_bad_aux_odd_sub {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [Nat.odd_iff]
  omega

theorem not_isUFourOdd_of_bad_aux_odd_add {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k + 1) := by
  have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  rw [Nat.odd_iff]
  omega

theorem not_isUFourOdd_of_bad_aux_two_pow_mul_odd_inj {a b u w : ℕ} (hu : Odd u) (hw : Odd w)
    (h : 2 ^ a * u = 2 ^ b * w) : a = b := by
  have hu0 : u ≠ 0 := hu.pos.ne'
  have hw0 : w ≠ 0 := hw.pos.ne'
  have h2u : ¬ 2 ∣ u := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hu
  have h2w : ¬ 2 ∣ w := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hw
  have := congrArg (padicValNat 2) h
  rw [padicValNat.mul (by positivity) hu0, padicValNat.mul (by positivity) hw0,
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd h2u,
    padicValNat.eq_zero_of_not_dvd h2w] at this
  simpa using this

theorem not_isUFourOdd_of_bad_aux_toNat_even {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  have : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have e : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub this]; ring
  rw [e]; exact Int.toNat_natCast _

theorem not_isUFourOdd_of_bad_aux_toNat_odd {q i : ℕ} (hi : Odd i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow]
  have e : ((q : ℤ) ^ i - -1) = ((q ^ i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e]; exact Int.toNat_natCast _

theorem not_isUFourOdd_of_bad_aux_ordU4 {n : ℕ} (hn : 1 ≤ n) :
    ordTwistedA 3 (2 ^ n) =
      2 ^ (6 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) * (2 ^ (4 * n) - 1)) := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hg : Nat.gcd 4 (2 ^ n + 1) = 1 := by
    have h2 : Nat.Coprime 2 (2 ^ n + 1) :=
      Nat.coprime_two_left.2 (not_isUFourOdd_of_bad_aux_odd_add hn)
    simpa using Nat.Coprime.pow_left 2 h2
  unfold ordTwistedA
  rw [show 3 * (3 + 1) / 2 = 6 by rfl, show Finset.Icc 2 (3 + 1) = {2, 3, 4} by rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  rw [not_isUFourOdd_of_bad_aux_toNat_even hq (by decide),
    not_isUFourOdd_of_bad_aux_toNat_odd (by decide),
    not_isUFourOdd_of_bad_aux_toNat_even hq (by decide)]
  rw [show (3 + 1 : ℕ) = 4 from rfl, hg, Nat.div_one]
  simp only [← pow_mul]
  ring_nf

theorem not_isUFourOdd_of_bad_aux_ordSp6 {m : ℕ} (hm : 1 ≤ m) :
    ordBC 3 (2 ^ m) =
      2 ^ (9 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1) * (2 ^ (6 * m) - 1)) := by
  have hg : Nat.gcd 2 (2 ^ m - 1) = 1 :=
    Nat.coprime_two_left.2 (not_isUFourOdd_of_bad_aux_odd_sub hm)
  unfold ordBC
  rw [show Finset.Icc 1 3 = {1, 2, 3} by rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  rw [hg, Nat.div_one]
  simp only [← pow_mul]
  ring_nf

theorem not_isUFourOdd_of_bad_aux_ordO8m {m : ℕ} (hm : 1 ≤ m) :
    ordTwistedD 4 (2 ^ m) =
      2 ^ (12 * m) * ((2 ^ (4 * m) + 1) *
        ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1) * (2 ^ (6 * m) - 1))) := by
  have hg : Nat.gcd 4 ((2 ^ m) ^ 4 + 1) = 1 := by
    have h2 : Nat.Coprime 2 ((2 ^ m) ^ 4 + 1) := by
      rw [← pow_mul]
      exact Nat.coprime_two_left.2 (not_isUFourOdd_of_bad_aux_odd_add (by omega))
    simpa using Nat.Coprime.pow_left 2 h2
  unfold ordTwistedD
  rw [show 4 - 1 = 3 by rfl, show Finset.Icc 1 3 = {1, 2, 3} by rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  rw [hg, Nat.div_one]
  simp only [← pow_mul]
  ring_nf

theorem not_isUFourOdd_of_bad_aux_odd_U4 {n : ℕ} (hn : 1 ≤ n) :
    Odd ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) * (2 ^ (4 * n) - 1)) :=
  (((not_isUFourOdd_of_bad_aux_odd_sub (by omega)).mul
    (not_isUFourOdd_of_bad_aux_odd_add (by omega))).mul
    (not_isUFourOdd_of_bad_aux_odd_sub (by omega)))

theorem not_isUFourOdd_of_bad_aux_odd_Sp6 {m : ℕ} (hm : 1 ≤ m) :
    Odd ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1) * (2 ^ (6 * m) - 1)) :=
  (((not_isUFourOdd_of_bad_aux_odd_sub (by omega)).mul
    (not_isUFourOdd_of_bad_aux_odd_sub (by omega))).mul
    (not_isUFourOdd_of_bad_aux_odd_sub (by omega)))

theorem not_isUFourOdd_of_bad_aux_odd_O8m {m : ℕ} (hm : 1 ≤ m) :
    Odd ((2 ^ (4 * m) + 1) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1) * (2 ^ (6 * m) - 1))) :=
  (not_isUFourOdd_of_bad_aux_odd_add (by omega)).mul (not_isUFourOdd_of_bad_aux_odd_Sp6 hm)

theorem not_isUFourOdd_of_bad_aux_ne_L6 {n : ℕ} (hn : 1 ≤ n) :
    ordTwistedA 3 (2 ^ n) ≠ ordA 5 2 := by
  intro h
  rw [not_isUFourOdd_of_bad_aux_ordU4 hn, show ordA 5 2 = 2 ^ 15 * 615195 by decide] at h
  have := not_isUFourOdd_of_bad_aux_two_pow_mul_odd_inj
    (not_isUFourOdd_of_bad_aux_odd_U4 hn) (by decide) h
  omega

theorem not_isUFourOdd_of_bad_aux_ne_L7 {n : ℕ} (hn : 1 ≤ n) :
    ordTwistedA 3 (2 ^ n) ≠ ordA 6 2 := by
  intro h
  rw [not_isUFourOdd_of_bad_aux_ordU4 hn, show ordA 6 2 = 2 ^ 21 * 78129765 by decide] at h
  have := not_isUFourOdd_of_bad_aux_two_pow_mul_odd_inj
    (not_isUFourOdd_of_bad_aux_odd_U4 hn) (by decide) h
  omega

theorem not_isUFourOdd_of_bad_aux_ne_O8m {n m : ℕ} (hn : Odd n) (hm : 1 ≤ m) :
    ordTwistedA 3 (2 ^ n) ≠ ordTwistedD 4 (2 ^ m) := by
  intro h
  have hn1 : 1 ≤ n := hn.pos
  rw [not_isUFourOdd_of_bad_aux_ordU4 hn1, not_isUFourOdd_of_bad_aux_ordO8m hm] at h
  have := not_isUFourOdd_of_bad_aux_two_pow_mul_odd_inj
    (not_isUFourOdd_of_bad_aux_odd_U4 hn1) (not_isUFourOdd_of_bad_aux_odd_O8m hm) h
  obtain ⟨k, hk⟩ := hn
  omega

theorem not_isUFourOdd_of_bad_aux_lt_Sp6 {k : ℕ} (hk : 1 ≤ k) :
    (2 ^ (4 * k) - 1) * (2 ^ (8 * k) - 1) * (2 ^ (12 * k) - 1) <
      (2 ^ (6 * k) - 1) * (2 ^ (9 * k) + 1) * (2 ^ (12 * k) - 1) := by
  have h46 : 2 ^ (4 * k) < 2 ^ (6 * k) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h89 : 2 ^ (8 * k) < 2 ^ (9 * k) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h4 : 1 ≤ 2 ^ (4 * k) := Nat.one_le_two_pow
  have h12 : 1 < 2 ^ (12 * k) := Nat.one_lt_two_pow (by omega)
  have h8 : 0 < 2 ^ (8 * k) := Nat.two_pow_pos _
  have h9 : 0 < 2 ^ (9 * k) := Nat.two_pow_pos _
  exact Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul'' (by omega) (by omega)) (by omega)

theorem not_isUFourOdd_of_bad_aux_ne_Sp6 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ordTwistedA 3 (2 ^ n) ≠ ordBC 3 (2 ^ m) := by
  intro h
  rw [not_isUFourOdd_of_bad_aux_ordU4 hn, not_isUFourOdd_of_bad_aux_ordSp6 hm] at h
  have h69 := not_isUFourOdd_of_bad_aux_two_pow_mul_odd_inj
    (not_isUFourOdd_of_bad_aux_odd_U4 hn) (not_isUFourOdd_of_bad_aux_odd_Sp6 hm) h
  rw [h69] at h
  have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
  have e2 : 2 * n = 6 * (m / 2) := by omega
  have e3 : 3 * n = 9 * (m / 2) := by omega
  have e4 : 4 * n = 12 * (m / 2) := by omega
  have f2 : 2 * m = 4 * (m / 2) := by omega
  have f4 : 4 * m = 8 * (m / 2) := by omega
  have f6 : 6 * m = 12 * (m / 2) := by omega
  rw [e2, e3, e4, f2, f4, f6] at h'
  exact (not_isUFourOdd_of_bad_aux_lt_Sp6 (k := m / 2) (by omega)).ne' h'

theorem not_isUFourOdd_of_bad_aux_card_U4 {S : Type} [Group S] (h : IsUFourOdd S) :
    ∃ n : ℕ, Odd n ∧ Nat.card S = ordTwistedA 3 (2 ^ n) := by
  obtain ⟨d, Q, hQ, hodd, hd, ⟨e⟩⟩ := h
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 Q hv e
  rw [hQ] at hm
  exact ⟨Q.exponent, hodd, (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.1 rfl⟩

theorem not_isUFourOdd_of_bad_aux_card_linTwo {m : ℕ} {S : Type} [Group S] (h : IsLinTwo m S) :
    Nat.card S = ordA (m - 1) 2 := by
  obtain ⟨Q, hQ2, hQc, d, hd, ⟨e⟩⟩ := h
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  rw [hQ2] at hm
  have h2 : 2 ^ Q.exponent = 2 := by
    have hc := TauCeti.PrimePower.card_def Q
    rw [hQ2] at hc
    rw [← hc]
    exact hQc
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hm).1 rfl, h2]
  simp

theorem not_isUFourOdd_of_bad_aux_card_sp {c : ℕ → Prop} {S : Type} [Group S]
    (h : IsSpSix c S) : ∃ m : ℕ, 1 ≤ m ∧ Nat.card S = ordBC 3 (2 ^ m) := by
  obtain ⟨Q, hQ2, -, d, hd, ⟨e⟩⟩ := h
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 Q hv hQ2 (le_refl 3) e
  rw [hQ2] at hm
  exact ⟨Q.exponent, Q.exponent_pos, (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.1 rfl⟩

theorem not_isUFourOdd_of_bad_aux_card_om {c : ℕ → Prop} {S : Type} [Group S]
    (h : IsOmegaEightMinus c S) : ∃ m : ℕ, 1 ≤ m ∧ Nat.card S = ordTwistedD 4 (2 ^ m) := by
  obtain ⟨Q, hQ2, -, d, hd, ⟨e⟩⟩ := h
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 Q hv hQ2 e
  rw [hQ2] at hm
  exact ⟨Q.exponent, Q.exponent_pos,
    (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.2.2 rfl⟩

theorem not_isUFourOdd_of_bad {p : ℕ} {S : Type} [Group S] [Finite S] (h : Bad1517 p S) :
    ¬ IsUFourOdd S := by
  intro hU
  obtain ⟨n, hn, hcU⟩ := not_isUFourOdd_of_bad_aux_card_U4 hU
  have hn1 : 1 ≤ n := hn.pos
  rcases h with ⟨hlin, -⟩ | hsp | hom
  · rcases hlin with h6 | h7
    · exact not_isUFourOdd_of_bad_aux_ne_L6 hn1
        (hcU.symm.trans (not_isUFourOdd_of_bad_aux_card_linTwo h6))
    · exact not_isUFourOdd_of_bad_aux_ne_L7 hn1
        (hcU.symm.trans (not_isUFourOdd_of_bad_aux_card_linTwo h7))
  · obtain ⟨m, hm, hcS⟩ := not_isUFourOdd_of_bad_aux_card_sp hsp
    exact not_isUFourOdd_of_bad_aux_ne_Sp6 hn1 hm (hcU.symm.trans hcS)
  · obtain ⟨m, hm, hcS⟩ := not_isUFourOdd_of_bad_aux_card_om hom
    exact not_isUFourOdd_of_bad_aux_ne_O8m hn hm (hcU.symm.trans hcS)

end CFSG.LocalAnalysis.RankThreeUC.S15
