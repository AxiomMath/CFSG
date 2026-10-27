module

public import CFSG.GH74.Generic.BProg.B2.ListedG5
public import CFSG.GH74.Generic.S3.L3ClassC2T2
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.GH74.Generic.BProg.B2

namespace T1G2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem key_int (x A N : ℤ) (hA : 9 ≤ A) (hx : A ≤ x + 1) (hN : 9 * N ≤ A ^ 3)
    (h2 : 2 * N = x * (x ^ 2 - 1)) : False := by
  have hx1 : A - 1 ≤ x := by linarith
  have hmono : (A - 1) * ((A - 1) ^ 2 - 1) ≤ x * (x ^ 2 - 1) := by
    have e : x * (x ^ 2 - 1) - (A - 1) * ((A - 1) ^ 2 - 1) =
        (x - (A - 1)) * (x ^ 2 + x * (A - 1) + (A - 1) ^ 2 - 1) := by ring
    have h0 : 0 ≤ x ^ 2 + x * (A - 1) + (A - 1) ^ 2 - 1 := by nlinarith
    have : 0 ≤ (x - (A - 1)) * (x ^ 2 + x * (A - 1) + (A - 1) ^ 2 - 1) :=
      mul_nonneg (by linarith) h0
    linarith
  nlinarith

theorem ordA_one_ne_of_pow {p f a b N q' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ p ^ f)
    (ha : 2 ≤ a) (hdvd : (p ^ f) ^ a ∣ N) (hN : N ≤ (p ^ f) ^ b) (hab : b + 2 ≤ 3 * a)
    (hN0 : 0 < N) (hq' : Odd q') : ordA 1 q' ≠ N := by
  intro hEq
  have h2N : 2 * N = q' * (q' ^ 2 - 1) := by
    rw [← hEq]; exact Generic.S3.L3Ord.two_mul_ordA_one hq'
  have hq1 : 1 ≤ q' := hq'.pos
  have hsq : q' ^ 2 - 1 = (q' - 1) * (q' + 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, q' = m + 1 := ⟨q' - 1, by omega⟩
    rw [Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 2) + 1 by ring]; simp
  have hA : (p ^ f) ^ a = p ^ (f * a) := by rw [← pow_mul]
  have hdvd2 : p ^ (f * a) ∣ q' * ((q' - 1) * (q' + 1)) := by
    rw [← hA, ← hsq, ← h2N]; exact Dvd.dvd.mul_left hdvd 2
  have hq3 : 3 ≤ q' := by
    by_contra hlt
    have : q' ≤ 2 := by omega
    interval_cases q'
    · simp at h2N; omega
    · exact absurd hq' (by decide)
  have hle : (p ^ f) ^ a ≤ q' + 1 := by
    rw [hA]
    rcases Generic.S3.L3Ord.pow_dvd_trichotomy hp hp2 hq1 hdvd2 with h | h | h
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h
  have h9 : 9 ≤ (p ^ f) ^ 2 :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left h3 2
  have hA9 : 9 ≤ (p ^ f) ^ a := h9.trans (Nat.pow_le_pow_right (by omega) ha)
  have hcube : 9 * N ≤ ((p ^ f) ^ a) ^ 3 := by
    calc 9 * N ≤ (p ^ f) ^ 2 * (p ^ f) ^ b := Nat.mul_le_mul h9 hN
      _ = (p ^ f) ^ (b + 2) := by rw [← pow_add, add_comm]
      _ ≤ (p ^ f) ^ (3 * a) := Nat.pow_le_pow_right (by omega) hab
      _ = ((p ^ f) ^ a) ^ 3 := by rw [mul_comm 3 a, pow_mul]
  apply key_int (q' : ℤ) (((p ^ f) ^ a : ℕ) : ℤ) (N : ℤ)
  · exact_mod_cast hA9
  · exact_mod_cast hle
  · exact_mod_cast hcube
  · have h1 : 1 ≤ q' ^ 2 := Nat.one_le_pow _ _ (by omega)
    have := congrArg (fun n : ℕ => (n : ℤ)) h2N
    push_cast [Nat.cast_sub h1] at this
    exact this

@[expose] def BigOrder (N : ℕ) : Prop :=
  (50232960 < N ∨ N = 42456960) ∧ ∀ q' : ℕ, Odd q' → ordA 1 q' ≠ N

theorem toNat_even {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  have : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have e : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub this]; ring
  rw [e]; exact Int.toNat_natCast _

theorem toNat_odd {q i : ℕ} (hi : Odd i) : ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow]
  have e : ((q : ℤ) ^ i - -1) = ((q ^ i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e]; exact Int.toNat_natCast _

theorem ordA_four_eq (q : ℕ) :
    ordA 4 q = q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1)) / Nat.gcd 5 (q - 1) := by
  unfold ordA
  rw [show 4 * (4 + 1) / 2 = 10 by rfl, show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} by rfl]
  simp [Finset.prod_insert, mul_assoc]

theorem ordA_three_eq (q : ℕ) :
    ordA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) / Nat.gcd 4 (q - 1) := by
  unfold ordA
  rw [show 3 * (3 + 1) / 2 = 6 by rfl, show Finset.Icc 2 (3 + 1) = {2, 3, 4} by rfl]
  simp [Finset.prod_insert, mul_assoc]

theorem ordTwistedA_four_eq {q : ℕ} (hq : 1 ≤ q) :
    ordTwistedA 4 q =
      q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)) / Nat.gcd 5 (q + 1) := by
  unfold ordTwistedA
  rw [show 4 * (4 + 1) / 2 = 10 by rfl, show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} by rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  rw [toNat_even hq (by decide), toNat_odd (by decide), toNat_even hq (by decide), toNat_odd (by decide)]
  simp [mul_assoc]

theorem ordTwistedA_three_eq {q : ℕ} (hq : 1 ≤ q) :
    ordTwistedA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) / Nat.gcd 4 (q + 1) := by
  unfold ordTwistedA
  rw [show 3 * (3 + 1) / 2 = 6 by rfl, show Finset.Icc 2 (3 + 1) = {2, 3, 4} by rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  rw [toNat_even hq (by decide), toNat_odd (by decide), toNat_even hq (by decide)]
  simp [mul_assoc]

theorem coprime_gcd {p f n c : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    Nat.Coprime ((p ^ f) ^ c) (Nat.gcd n (p ^ f - 1)) ∧ Nat.Coprime ((p ^ f) ^ c) (Nat.gcd n (p ^ f + 1)) := by
  have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hpos : 0 < p ^ f := pow_pos hp.pos f
  have h1 : ¬ p ∣ p ^ f - 1 := fun hd => by
    have : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpq hd
    rw [show p ^ f - (p ^ f - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have h2 : ¬ p ∣ p ^ f + 1 := fun hd => by
    have : p ∣ p ^ f + 1 - p ^ f := Nat.dvd_sub hd hpq
    rw [show p ^ f + 1 - p ^ f = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  rw [← pow_mul]
  refine ⟨Nat.Coprime.pow_left _ ?_, Nat.Coprime.pow_left _ ?_⟩
  · rw [hp.coprime_iff_not_dvd]
    exact fun hd => h1 (hd.trans (Nat.gcd_dvd_right _ _))
  · rw [hp.coprime_iff_not_dvd]
    exact fun hd => h2 (hd.trans (Nat.gcd_dvd_right _ _))

theorem dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 ∧ q + 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    refine ⟨⟨m + 2, ?_⟩, ⟨m, ?_⟩⟩
    · rw [Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 2) + 1 by ring]; simp
    · rw [show (m + 1) ^ 2 = (m + 1 + 1) * m + 1 by ring]; simp

theorem bigOrder_of_mul {p f c d N g P k L : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : 3 ≤ p ^ f) (hc : 2 ≤ c) (hmul : N * g = (p ^ f) ^ c * P) (hg0 : 0 < g) (hgk : g ≤ k)
    (hcop : Nat.Coprime ((p ^ f) ^ c) g) (hP0 : 0 < P) (hPd : P ≤ (p ^ f) ^ d) (hcd : c + d + 2 ≤ 3 * c)
    (hL : 50232960 * k < L) (hLow : L ≤ (p ^ f) ^ c * P) : BigOrder N := by
  have hdvd : (p ^ f) ^ c ∣ N := hcop.dvd_of_dvd_mul_right ⟨P, by rw [hmul]⟩
  have hpos : 0 < (p ^ f) ^ c * P := Nat.mul_pos (by positivity) hP0
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, zero_mul] at hmul; omega
    · exact h
  have hNle : N ≤ (p ^ f) ^ (c + d) := by
    calc N ≤ N * g := Nat.le_mul_of_pos_right _ hg0
      _ = (p ^ f) ^ c * P := hmul
      _ ≤ (p ^ f) ^ c * (p ^ f) ^ d := Nat.mul_le_mul_left _ hPd
      _ = (p ^ f) ^ (c + d) := by rw [← pow_add]
  refine ⟨Or.inl ?_, fun q' hq' => ordA_one_ne_of_pow hp hp2 h3 hc hdvd hNle hcd hN0 hq'⟩
  have h1 : N * g ≤ N * k := Nat.mul_le_mul_left _ hgk
  have h2 : 50232960 * k < N * k := by
    calc 50232960 * k < L := hL
      _ ≤ (p ^ f) ^ c * P := hLow
      _ = N * g := hmul.symm
      _ ≤ N * k := h1
  exact Nat.lt_of_mul_lt_mul_right h2

theorem three_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) : 3 ≤ p ^ f := by
  have h2 := hp.two_le
  have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  omega

theorem bigOrder_psl5 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    BigOrder (ordA 4 (p ^ f)) := by
  have h3 := three_le_pow hp hp2 hf
  set q := p ^ f with hq
  have h2 : 9 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 2)
  have h3' : 27 ≤ q ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 3)
  have h4 : 81 ≤ q ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 4)
  have h5 : 243 ≤ q ^ 5 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 5)
  have h10 : 59049 ≤ q ^ 10 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 10)
  set P := (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1) with hP
  have hg : Nat.gcd 5 (q - 1) ∣ q ^ 10 * P :=
    ((Nat.gcd_dvd_right _ _).trans (dvd_sq_sub_one q).1).trans
      (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _) _) _)
  have hmul : ordA 4 q * Nat.gcd 5 (q - 1) = q ^ 10 * P := by
    rw [ordA_four_eq]; exact Nat.div_mul_cancel hg
  have hPlow : 8 * 26 * 80 * 242 ≤ P := by
    rw [hP]; gcongr <;> omega
  refine bigOrder_of_mul (c := 10) (d := 14) (k := 5) (L := 59049 * (8 * 26 * 80 * 242)) hp hp2 h3
    (by norm_num) hmul (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))
    (coprime_gcd hp hf).1 (by omega) ?_ (by norm_num) (by norm_num) (Nat.mul_le_mul h10 hPlow)
  calc P ≤ q ^ 2 * q ^ 3 * q ^ 4 * q ^ 5 := by rw [hP]; gcongr <;> omega
    _ = q ^ 14 := by ring

theorem bigOrder_psu5 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    BigOrder (ordTwistedA 4 (p ^ f)) := by
  have h3 := three_le_pow hp hp2 hf
  set q := p ^ f with hq
  have h2 : 9 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 2)
  have h3' : 27 ≤ q ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 3)
  have h4 : 81 ≤ q ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 4)
  have h5 : 243 ≤ q ^ 5 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 5)
  have h10 : 59049 ≤ q ^ 10 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 10)
  set P := (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) with hP
  have hg : Nat.gcd 5 (q + 1) ∣ q ^ 10 * P :=
    ((Nat.gcd_dvd_right _ _).trans (dvd_sq_sub_one q).2).trans
      (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _) _) _)
  have hmul : ordTwistedA 4 q * Nat.gcd 5 (q + 1) = q ^ 10 * P := by
    rw [ordTwistedA_four_eq (by omega)]; exact Nat.div_mul_cancel hg
  have hPlow : 8 * 28 * 80 * 244 ≤ P := by
    rw [hP]; gcongr <;> omega
  have e3 : q ^ 3 + 1 ≤ q ^ 4 := by
    have : q ^ 4 = q * q ^ 3 := by ring
    have : 3 * q ^ 3 ≤ q * q ^ 3 := Nat.mul_le_mul_right _ h3
    omega
  have e5 : q ^ 5 + 1 ≤ q ^ 6 := by
    have : q ^ 6 = q * q ^ 5 := by ring
    have : 3 * q ^ 5 ≤ q * q ^ 5 := Nat.mul_le_mul_right _ h3
    omega
  refine bigOrder_of_mul (c := 10) (d := 16) (k := 5) (L := 59049 * (8 * 28 * 80 * 244)) hp hp2 h3
    (by norm_num) hmul (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))
    (coprime_gcd hp hf).2 (by omega) ?_ (by norm_num) (by norm_num) (Nat.mul_le_mul h10 hPlow)
  calc P ≤ q ^ 2 * q ^ 4 * q ^ 4 * q ^ 6 := by rw [hP]; gcongr <;> omega
    _ = q ^ 16 := by ring

theorem bigOrder_psl4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) :
    BigOrder (ordA 3 (p ^ f)) := by
  have h3 := three_le_pow hp hp2 hf
  set q := p ^ f with hq
  have h2 : 25 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left h5 2)
  have h3' : 125 ≤ q ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left h5 3)
  have h4 : 625 ≤ q ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left h5 4)
  have h6 : 15625 ≤ q ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left h5 6)
  set P := (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) with hP
  have hg : Nat.gcd 4 (q - 1) ∣ q ^ 6 * P :=
    ((Nat.gcd_dvd_right _ _).trans (dvd_sq_sub_one q).1).trans
      (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _) _)
  have hmul : ordA 3 q * Nat.gcd 4 (q - 1) = q ^ 6 * P := by
    rw [ordA_three_eq]; exact Nat.div_mul_cancel hg
  have hPlow : 24 * 124 * 624 ≤ P := by
    rw [hP]; gcongr <;> omega
  refine bigOrder_of_mul (c := 6) (d := 9) (k := 4) (L := 15625 * (24 * 124 * 624)) hp hp2 h3
    (by norm_num) hmul (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))
    (coprime_gcd hp hf).1 (by omega) ?_ (by norm_num) (by norm_num) (Nat.mul_le_mul h6 hPlow)
  calc P ≤ q ^ 2 * q ^ 3 * q ^ 4 := by rw [hP]; gcongr <;> omega
    _ = q ^ 9 := by ring

theorem bigOrder_psu4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) :
    BigOrder (ordTwistedA 3 (p ^ f)) := by
  have h3 := three_le_pow hp hp2 hf
  set q := p ^ f with hq
  have h2 : 25 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left h5 2)
  have h3' : 125 ≤ q ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left h5 3)
  have h4 : 625 ≤ q ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left h5 4)
  have h6 : 15625 ≤ q ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left h5 6)
  set P := (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) with hP
  have hg : Nat.gcd 4 (q + 1) ∣ q ^ 6 * P :=
    ((Nat.gcd_dvd_right _ _).trans (dvd_sq_sub_one q).2).trans
      (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _) _)
  have hmul : ordTwistedA 3 q * Nat.gcd 4 (q + 1) = q ^ 6 * P := by
    rw [ordTwistedA_three_eq (by omega)]; exact Nat.div_mul_cancel hg
  have hPlow : 24 * 126 * 624 ≤ P := by
    rw [hP]; gcongr <;> omega
  have e3 : q ^ 3 + 1 ≤ q ^ 4 := by
    have : q ^ 4 = q * q ^ 3 := by ring
    have : 3 * q ^ 3 ≤ q * q ^ 3 := Nat.mul_le_mul_right _ h3
    omega
  refine bigOrder_of_mul (c := 6) (d := 10) (k := 4) (L := 15625 * (24 * 126 * 624)) hp hp2 h3
    (by norm_num) hmul (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))
    (coprime_gcd hp hf).2 (by omega) ?_ (by norm_num) (by norm_num) (Nat.mul_le_mul h6 hPlow)
  calc P ≤ q ^ 2 * q ^ 4 * q ^ 4 := by rw [hP]; gcongr <;> omega
    _ = q ^ 10 := by ring

theorem bigOrder_g2 {f : ℕ} (hf : 3 ≤ f) : BigOrder (ordG2 (3 ^ f)) := by
  have h27 : 27 ≤ 3 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  set q := 3 ^ f with hq
  have h2 : 729 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left h27 2)
  have h6 : 387420489 ≤ q ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left h27 6)
  set P := (q ^ 6 - 1) * (q ^ 2 - 1) with hP
  have hmul : ordG2 q * 1 = q ^ 6 * P := by
    rw [mul_one, ordG2, hP, mul_assoc]
  have hPlow : 1 ≤ P := by
    rw [hP]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine bigOrder_of_mul (p := 3) (c := 6) (d := 8) (k := 1) (L := 387420489 * 1) Nat.prime_three
    (by norm_num) (by omega) (by norm_num) hmul (by norm_num) le_rfl
    (Nat.coprime_one_right _) (by omega) ?_ (by norm_num) (by norm_num) (Nat.mul_le_mul h6 hPlow)
  calc P ≤ q ^ 6 * q ^ 2 := by rw [hP]; gcongr <;> omega
    _ = q ^ 8 := by ring

theorem card_le_of_evenLieType
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (hE : EvenLieType S) (hgen : Gen4 S) : Nat.card S ≤ 62400 := by
  have hPSU : ∀ {n f : ℕ}, n ≠ 0 → LieModel S .PSU n 2 f → Nat.card S = ordTwistedA (n - 1) (2 ^ f) :=
    fun hn h => (Timmesfeld.card_statedClassicalModel_two (statedClassicalModel_of_lieModel hn h)).2.1 rfl
  rcases E2.evenLieRankFour S hs hnab hE hgen with
    hA5 | hL27 | hL28 | hSz | h216 | h34 | h42 | hU34 | hU42
  · rcases hA5 with he | h | h
    · obtain ⟨e⟩ := he
      have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
      rw [Nat.card_congr e.toEquiv, h60]; norm_num
    · rw [card_of_lieModel_PSL (n := 2) (by norm_num) h]; decide
    · rw [card_of_lieModel_PSL (n := 2) (by norm_num) h]; decide
  · rcases hL27 with h | h
    · rw [card_of_lieModel_PSL (n := 2) (by norm_num) h]; decide
    · rw [card_of_lieModel_PSL (n := 3) (by norm_num) h]; decide
  · rw [card_of_lieModel_PSL (n := 2) (by norm_num) hL28]; decide
  · rw [card_of_lieModel_twistedB2 hSz]; decide
  · rw [card_of_lieModel_PSL (n := 2) (by norm_num) h216]; decide
  · rw [card_of_lieModel_PSL (n := 3) (by norm_num) h34]; decide
  · rw [card_of_lieModel_PSL (n := 4) (by norm_num) h42]; decide
  · rw [hPSU (by norm_num) hU34]; decide
  · rw [hPSU (by norm_num) hU42]; decide

theorem simpleInC2_cases
    {S : Type} [Group S] [Finite S] (hS : SimpleInC2 S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (hgen : Gen4 S) :
    (∃ q' : ℕ, Odd q' ∧ Nat.card S = ordA 1 q') ∨ (Nat.card S ≤ 50232960 ∧ Nat.card S ≠ 42456960) := by
  obtain ⟨hs, hc⟩ := hS
  have small : ∀ n : ℕ, Nat.card S = n → n ≤ 50232960 → n ≠ 42456960 →
      (∃ q' : ℕ, Odd q' ∧ Nat.card S = ordA 1 q') ∨ (Nat.card S ≤ 50232960 ∧ Nat.card S ≠ 42456960) :=
    fun n h h1 h2 => Or.inr ⟨h ▸ h1, h ▸ h2⟩
  have large : ∀ s : TauCeti.SporadicName, s ∈ Filter.sporadicOut → NativeSporadic.IsSporadic S s → False :=
    fun s hs' h => Filter.t_sporadic_all Filter.t_sporadic_M s hs' S hnab h hgen
  rcases hc with hChev | hL2 | hL33 | hL43 | hU43 | hG23 | hM11 | hM12 | hM22 | hM23 | hM24 |
    hJ2 | hJ3 | hJ4 | hHS | hSuz | hRu | hCo1 | hCo2 | hFi22 | hFi23 | hFi24 | hTh | hB | hM
  · rcases hChev with hE | he | hU33
    · have := card_le_of_evenLieType hs hnab hE hgen
      exact Or.inr ⟨by omega, by omega⟩
    · obtain ⟨e⟩ := he
      have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
      exact small 360 ((Nat.card_congr e.toEquiv).trans h360) (by norm_num) (by norm_num)
    · exact small _ (card_of_lieModel_PSU (n := 3) (by norm_num) (by norm_num) hU33) (by decide) (by decide)
  · obtain ⟨p, f, hp, hf, hfm, hL⟩ := hL2
    have hp2 : p ≠ 2 := E2.isFM9_ne_two hf hfm
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    refine Or.inl ⟨p ^ f, hodd, ?_⟩
    have hc := card_of_lieModel_PSL (n := 2) (by norm_num) hL
    simpa using hc
  · exact small _ (card_of_lieModel_PSL (n := 3) (by norm_num) hL33) (by decide) (by decide)
  · exact small _ (card_of_lieModel_PSL (n := 4) (by norm_num) hL43) (by decide) (by decide)
  · exact small _ (card_of_lieModel_PSU (n := 4) (by norm_num) (by norm_num) hU43) (by decide) (by decide)
  · exact small _ (card_of_lieModel_G2 (p := 3) (by norm_num) hG23) (by decide) (by decide)
  · exact small _ (card_eq_of_isSporadic (s := .M11) Sporadic.Mathieu.card_M11 hM11) (by norm_num)
      (by norm_num)
  · exact small _ (card_of_isSporadic_M12 hM12) (by norm_num) (by norm_num)
  · exact small _ (card_of_isSporadic_M22 hM22) (by norm_num) (by norm_num)
  · exact small _ (card_of_isSporadic_M23 hM23) (by norm_num) (by norm_num)
  · exact (large _ (by decide) hM24).elim
  · exact small _ (card_of_isSporadic_J2 hJ2) (by norm_num) (by norm_num)
  · exact small _ (card_of_isSporadic_J3 hJ3) (by norm_num) (by norm_num)
  · exact (large _ (by decide) hJ4).elim
  · exact (large _ (by decide) hHS).elim
  · exact (large _ (by decide) hSuz).elim
  · exact (large _ (by decide) hRu).elim
  · exact (large _ (by decide) hCo1).elim
  · exact (large _ (by decide) hCo2).elim
  · exact (large _ (by decide) hFi22).elim
  · exact (large _ (by decide) hFi23).elim
  · exact (large _ (by decide) hFi24).elim
  · exact (large _ (by decide) hTh).elim
  · exact (large _ (by decide) hB).elim
  · exact (large _ (by decide) hM).elim

theorem not_inC2_not_inT2_of_bigOrder
    {J : Type} [Group J] [Finite J] (hs : IsSimpleGroup J) (hnab : ∃ a b : J, a * b ≠ b * a)
    (hgen : Gen4 J) (hB : BigOrder (Nat.card J)) : ¬ InC2 J ∧ ¬ InT2 J := by
  have hcen : center J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center J) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ center J := by rw [h]; exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.1 ha b).symm)
  obtain ⟨hbig, hL2⟩ := hB
  refine ⟨fun hC => ?_, fun hT => ?_⟩
  · obtain ⟨-, -, hS, -⟩ := hC
    let e : (J ⧸ center J) ≃* J := (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    have hcard : Nat.card (J ⧸ center J) = Nat.card J := Nat.card_congr e.toEquiv
    have hnab' : ∃ a b : J ⧸ center J, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
      have := congrArg e h
      simpa using this
    have hgen' : Gen4 (J ⧸ center J) := Gen4.of_mulEquiv e.symm hgen
    rcases simpleInC2_cases hS hnab' hgen' with ⟨q', hq', hc⟩ | ⟨h1, h2⟩
    · exact hL2 q' hq' (hc.symm.trans hcard)
    · rw [hcard] at h1 h2
      omega
  · rcases inT2_cases_of_center_bot hT hcen with ⟨p, f, hp, hf, ⟨hodd, -⟩, hL⟩ | he
    · have hc := card_of_lieModel_PSL (n := 2) (by norm_num) hL
      exact hL2 (p ^ f) hodd (by simpa using hc.symm)
    · obtain ⟨e⟩ := he
      have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
      have := (Nat.card_congr e.toEquiv).trans h7
      omega

theorem bigOrder_of_puL3sq {J : Type} [Group J] [Finite J] (h : PuL3sq J) : BigOrder (Nat.card J) := by
  obtain ⟨p, f, hp, hp2, hf, hL⟩ := h
  have h3 := three_le_pow hp hp2 hf
  have hQ : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [mul_comm, pow_mul]
  have h9 : 9 ≤ p ^ (2 * f) := by rw [hQ]; exact le_trans (by norm_num) (Nat.pow_le_pow_left h3 2)
  obtain ⟨-, h2, h3'⟩ := Generic.S3.l3_card_bounds (t := .PSL) (Or.inl rfl) hp hp2 (by omega) hL
  refine ⟨?_, fun q' hq' => Generic.S3.L3Ord.ordA_one_ne hp hp2 (by omega) h2 ?_ h3' hq'⟩
  · have hc := card_of_lieModel_PSL (n := 3) (by norm_num) hL
    simp only [show 3 - 1 = 2 from rfl] at hc
    rw [hc]
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    by_cases h3e : p ^ f = 3
    · right
      rw [hQ, h3e]; decide
    · left
      have h5 : 5 ≤ p ^ f := by
        obtain ⟨k, hk⟩ := hodd
        omega
      set Q := p ^ (2 * f) with hQdef
      have h25 : 25 ≤ Q := by rw [hQ]; exact le_trans (by norm_num) (Nat.pow_le_pow_left h5 2)
      have hmul := Generic.S3.L3Ord.ordA_two_mul Q (by omega)
      have hg : Nat.gcd 3 (Q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
      have e2 : 624 ≤ Q ^ 2 - 1 := by
        have : 25 ^ 2 ≤ Q ^ 2 := Nat.pow_le_pow_left h25 2
        omega
      have e3 : 15624 ≤ Q ^ 3 - 1 := by
        have : 25 ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left h25 3
        omega
      have e3' : 15625 ≤ Q ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left h25 3)
      have hlow : 15625 * (624 * 15624) ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) :=
        Nat.mul_le_mul e3' (Nat.mul_le_mul e2 e3)
      have h1 : ordA 2 Q * Nat.gcd 3 (Q - 1) ≤ ordA 2 Q * 3 := Nat.mul_le_mul_left _ hg
      omega
  · have := Nat.card_pos (α := J)
    omega

theorem bigOrder_of_puTargetG4
    {J : Type} [Group J] [Finite J] (h : PuTargetG4 J) : BigOrder (Nat.card J) := by
  rcases h with ⟨p, f, hp, hp2, hf, ⟨-, hL⟩ | ⟨-, hU⟩⟩ |
      ⟨p, f, hp, hp2, hf, h3, ⟨-, hL⟩ | ⟨-, hU⟩⟩ | h3sq | ⟨f, hf, -, hG⟩
  · rw [card_of_lieModel_PSL (n := 5) (by norm_num) hL]
    exact bigOrder_psl5 hp hp2 hf
  · rw [card_of_lieModel_PSU (n := 5) (by norm_num) hp2 hU]
    exact bigOrder_psu5 hp hp2 hf
  · have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h5 : 5 ≤ p ^ f := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rw [card_of_lieModel_PSL (n := 4) (by norm_num) hL]
    exact bigOrder_psl4 hp hp2 hf h5
  · have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h5 : 5 ≤ p ^ f := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rw [card_of_lieModel_PSU (n := 4) (by norm_num) hp2 hU]
    exact bigOrder_psu4 hp hp2 hf h5
  · exact bigOrder_of_puL3sq h3sq
  · rw [card_of_lieModel_G2 (p := 3) (by norm_num) hG]
    exact bigOrder_g2 hf

theorem not_inC2_not_inT2_of_puTargetG4
    {J : Type} [Group J] [Finite J] (hs : IsSimpleGroup J) (hnab : ∃ a b : J, a * b ≠ b * a)
    (hgen : Gen4 J) (h : PuTargetG4 J) : ¬ InC2 J ∧ ¬ InT2 J :=
  not_inC2_not_inT2_of_bigOrder hs hnab hgen (bigOrder_of_puTargetG4 h)

end T1G2

end CFSG.GH74.Generic.BProg.B2
