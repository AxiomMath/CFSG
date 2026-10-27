module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05NonIsoArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM11

theorem coprime_of_dvd_four {p g : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hg : g ∣ 4) :
    Nat.Coprime p g :=
  Nat.Coprime.coprime_dvd_right hg ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega)

theorem coprime_odd_of_dvd_four {s d : ℕ} (hs : Odd s) (hd : d ∣ 4) : Nat.Coprime s d := by
  have h2 : Nat.Coprime s 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (by rw [Nat.two_dvd_ne_zero]; exact Nat.odd_iff.1 hs)).symm
  have h4 : Nat.Coprime s 4 := by
    have := Nat.Coprime.pow_right 2 h2
    norm_num at this
    exact this
  exact Nat.Coprime.coprime_dvd_right hd h4

theorem c1 {p x : ℕ} (hp5 : 5 ≤ p) (h1 : p ∣ x) (h2 : p ∣ x + 2) : False := by
  have h : p ∣ 2 := (Nat.dvd_add_right h1).1 h2
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem c2 {p x : ℕ} (hp5 : 5 ≤ p) (h1 : p ∣ x) (h2 : p ∣ x * (x + 3) + 3) : False := by
  have h : p ∣ 3 := (Nat.dvd_add_right (Dvd.dvd.mul_right h1 _)).1 h2
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem c3 {p x : ℕ} (hp : p.Prime) (h1 : p ∣ x + 2) (h2 : p ∣ (x + 2) * (x + 1) + 1) : False := by
  have h : p ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_right h1 _)).1 h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h)

theorem c4 {p x : ℕ} (hp5 : 5 ≤ p) (h1 : p ∣ x) (h2 : p ∣ x * (x + 2) + 2) : False := by
  have h : p ∣ 2 := (Nat.dvd_add_right (Dvd.dvd.mul_right h1 _)).1 h2
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem c5 {p x : ℕ} (hp5 : 5 ≤ p) (h1 : p ∣ x + 2) (h2 : p ∣ x * (x + 2) + 2) : False := by
  have h : p ∣ 2 := (Nat.dvd_add_right (Dvd.dvd.mul_left h1 x)).1 h2
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem c6 {p x : ℕ} (hp : p.Prime) (h1 : p ∣ x * (x + 2) + 2)
    (h2 : p ∣ x * (x + 3) + 3) : False := by
  have hsum : x * (x + 3) + 3 = (x * (x + 2) + 2) + (x + 1) := by ring
  rw [hsum] at h2
  have h3 : p ∣ x + 1 := (Nat.dvd_add_right h1).1 h2
  have h4 : p ∣ (x + 1) * (x + 1) + 1 := by
    have : (x + 1) * (x + 1) + 1 = (x * (x + 2) + 2) := by ring
    rw [this]
    exact h1
  have h5 : p ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_right h3 _)).1 h4
  exact hp.one_lt.ne' (Nat.dvd_one.1 h5)

theorem nc_x3 {p x : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.gcd (x ^ 3) ((x + 2) * (x ^ 2 + 3 * x + 3)) := by
  intro h
  have h1 : p ∣ x ^ 3 := h.trans (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ (x + 2) * (x ^ 2 + 3 * x + 3) := h.trans (Nat.gcd_dvd_right _ _)
  have hx' : p ∣ x := hp.dvd_of_dvd_pow h1
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
  · exact c1 hp5 hx' h3
  · have hC : x ^ 2 + 3 * x + 3 = x * (x + 3) + 3 := by ring
    rw [hC] at h3
    exact c2 hp5 hx' h3

theorem nc_x2 {p x : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.gcd (x + 2) (x ^ 2 + 3 * x + 3) := by
  intro h
  have h1 : p ∣ x + 2 := h.trans (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ x ^ 2 + 3 * x + 3 := h.trans (Nat.gcd_dvd_right _ _)
  have hC : x ^ 2 + 3 * x + 3 = (x + 2) * (x + 1) + 1 := by ring
  rw [hC] at h2
  exact c3 hp h1 h2

theorem nc_x4 {p x : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.gcd (x ^ 4) ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3)) := by
  intro h
  have h1 : p ∣ x ^ 4 := h.trans (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ (x + 2) ^ 2 * (x ^ 2 + 3 * x + 3) := h.trans (Nat.gcd_dvd_right _ _)
  have hx' : p ∣ x := hp.dvd_of_dvd_pow h1
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
  · exact c1 hp5 hx' (hp.dvd_of_dvd_pow h3)
  · have hC : x ^ 2 + 3 * x + 3 = x * (x + 3) + 3 := by ring
    rw [hC] at h3
    exact c2 hp5 hx' h3

theorem nc_x22 {p x : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.gcd ((x + 2) ^ 2) (x ^ 2 + 3 * x + 3) := by
  intro h
  have h1 : p ∣ (x + 2) ^ 2 := h.trans (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ x ^ 2 + 3 * x + 3 := h.trans (Nat.gcd_dvd_right _ _)
  have hC : x ^ 2 + 3 * x + 3 = (x + 2) * (x + 1) + 1 := by ring
  rw [hC] at h2
  exact c3 hp (hp.dvd_of_dvd_pow h1) h2

theorem nc_D2 {p x : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.gcd (x * (x + 2) + 2) (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3))) := by
  intro h
  have h1 : p ∣ x * (x + 2) + 2 := h.trans (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3)) := h.trans (Nat.gcd_dvd_right _ _)
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
  · exact c4 hp5 (hp.dvd_of_dvd_pow h3) h1
  · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
    · exact c5 hp5 h4 h1
    · have hC : x ^ 2 + 3 * x + 3 = x * (x + 3) + 3 := by ring
      rw [hC] at h4
      exact c6 hp h1 h4

theorem sq_facts {s x : ℕ} (hx : s ^ 2 = x + 1) :
    s ^ 2 - 1 = x ∧ s ^ 4 - 1 = x * (x + 2) ∧ s ^ 6 - 1 = x * (x ^ 2 + 3 * x + 3) ∧
      s ^ 4 + 1 = x * (x + 2) + 2 ∧ s ^ 4 + s ^ 2 + 1 = x * (x + 3) + 3 := by
  have h4 : s ^ 4 = x * (x + 2) + 1 := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hx]
    ring
  have h6 : s ^ 6 = x * (x ^ 2 + 3 * x + 3) + 1 := by
    rw [show s ^ 6 = (s ^ 2) ^ 3 by ring, hx]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hx, Nat.add_sub_cancel]
  · rw [h4, Nat.add_sub_cancel]
  · rw [h6, Nat.add_sub_cancel]
  · rw [h4]
  · rw [h4, hx]
    ring

theorem blk_bounds {s x : ℕ} (hs : 2 ≤ s) (hx : s ^ 2 = x + 1) :
    x ^ 3 < s ^ 6 ∧ x + 2 < s ^ 6 ∧ x ^ 2 + 3 * x + 3 < s ^ 6 ∧ x ^ 2 + 2 * x + 2 < s ^ 6 ∧
      (x + 2) ^ 2 < s ^ 6 ∧ x ^ 4 < s ^ 8 := by
  have h4 : 4 ≤ s ^ 2 := by nlinarith
  have hx3 : 3 ≤ x := by omega
  have hxx : 3 * x ≤ x * x := Nat.mul_le_mul_right x hx3
  have hxxx : 3 * (x * x) ≤ x * (x * x) := Nat.mul_le_mul_right (x * x) hx3
  have e6 : s ^ 6 = (x + 1) ^ 3 := by rw [show s ^ 6 = (s ^ 2) ^ 3 by ring, hx]
  have e8 : s ^ 8 = (x + 1) ^ 4 := by rw [show s ^ 8 = (s ^ 2) ^ 4 by ring, hx]
  rw [e6, e8]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith [hxx, hxxx, Nat.zero_le (x ^ 2), Nat.zero_le (x ^ 3), Nat.zero_le (x ^ 4)]

theorem fx_A3_lt {q : ℕ} (hq : 2 ≤ q) : (q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)) < q ^ 9 := by
  have h2 : q ^ 2 - 1 < q ^ 2 := Nat.sub_lt (pow_pos (by omega) 2) one_pos
  have h3 : q ^ 3 - 1 < q ^ 3 := Nat.sub_lt (pow_pos (by omega) 3) one_pos
  have h4 : q ^ 4 - 1 < q ^ 4 := Nat.sub_lt (pow_pos (by omega) 4) one_pos
  calc (q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)) < q ^ 2 * (q ^ 3 * q ^ 4) :=
        Nat.mul_lt_mul'' h2 (Nat.mul_lt_mul'' h3 h4)
    _ = q ^ 9 := by ring

theorem fx_U4_lt {q : ℕ} (hq : 2 ≤ q) : (q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)) < q ^ 9 := by
  obtain ⟨y, hy⟩ : ∃ y, q ^ 2 = y + 1 :=
    ⟨q ^ 2 - 1, by have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hq2 : q ^ 2 - 1 = y := by rw [hy, Nat.add_sub_cancel]
  have hq4 : q ^ 4 - 1 = y * (y + 2) := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hy, show (y + 1) ^ 2 = y * (y + 2) + 1 by ring,
      Nat.add_sub_cancel]
  have hid : (y * (y * (y + 2))) + (q ^ 4 + q ^ 2) = q ^ 6 + 1 := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, show q ^ 6 = (q ^ 2) ^ 3 by ring, hy]
    ring
  have hP : (y * (y * (y + 2))) * (q ^ 3 + 1) + (q ^ 7 + q ^ 5 + q ^ 4 + q ^ 2) =
      q ^ 9 + q ^ 6 + q ^ 3 + 1 := by
    calc (y * (y * (y + 2))) * (q ^ 3 + 1) + (q ^ 7 + q ^ 5 + q ^ 4 + q ^ 2)
        = ((y * (y * (y + 2))) + (q ^ 4 + q ^ 2)) * (q ^ 3 + 1) := by ring
      _ = (q ^ 6 + 1) * (q ^ 3 + 1) := by rw [hid]
      _ = q ^ 9 + q ^ 6 + q ^ 3 + 1 := by ring
  have h7 : 2 * q ^ 6 ≤ q ^ 7 := by
    rw [show q ^ 7 = q * q ^ 6 by ring]
    exact Nat.mul_le_mul_right _ hq
  have h63 : q ^ 3 + 1 ≤ q ^ 6 := by
    have h3 : 8 ≤ q ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    rw [show q ^ 6 = q ^ 3 * q ^ 3 by ring]
    nlinarith
  have key : q ^ 6 + q ^ 3 + 1 < q ^ 7 + q ^ 5 + q ^ 4 + q ^ 2 := by
    have : 0 < q ^ 5 + q ^ 4 + q ^ 2 := by positivity
    omega
  have hval : (q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)) = (y * (y * (y + 2))) * (q ^ 3 + 1) := by
    rw [hq2, hq4]
    ring
  rw [hval]
  omega

theorem fx_A3_pos {q : ℕ} (hq : 2 ≤ q) : 0 < (q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)) := by
  have h2 : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have h3 : 0 < q ^ 3 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have h4 : 0 < q ^ 4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  exact Nat.mul_pos h2 (Nat.mul_pos h3 h4)

theorem fx_U4_pos {q : ℕ} (hq : 2 ≤ q) : 0 < (q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)) := by
  have h2 : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have h4 : 0 < q ^ 4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  exact Nat.mul_pos h2 (Nat.mul_pos (by omega) h4)

theorem lt_of_pow6 {u v : ℕ} (h : u ^ 6 < v ^ 6) : u < v :=
  (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num)).1 h

theorem lt_of_pow_le_lt {s q e : ℕ} (he : 9 ≤ e) (hs : 1 ≤ s) (h : s ^ e < q ^ 9) : s < q := by
  by_contra hc
  have h1 : q ^ 9 ≤ s ^ 9 := Nat.pow_le_pow_left (not_lt.1 hc) 9
  have h2 : s ^ 9 ≤ s ^ e := Nat.pow_le_pow_right hs he
  exact (not_lt.2 (h1.trans h2)) h

theorem cross_core {M p s a g d FX FY e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hs1 : 1 ≤ s)
    (hsodd : Odd s) (hps : ¬ p ∣ s) (hg : g ∣ 4) (hd : d ∣ 4)
    (hFX0 : 0 < FX) (hFX : FX < (p ^ a) ^ 9)
    (E1 : M * g = (p ^ a) ^ 6 * FX) (E2 : M * d = s ^ e * FY) (he : 9 ≤ e) :
    (p ^ a) ^ 6 ∣ FY ∧ s ^ e ≤ FX ∧ s < p ^ a := by
  have hcopg : Nat.Coprime ((p ^ a) ^ 6) g :=
    Nat.Coprime.pow_left 6 (Nat.Coprime.pow_left a (coprime_of_dvd_four hp hp5 hg))
  have hcopq_s : Nat.Coprime (p ^ a) s :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hps)
  have hcopse : Nat.Coprime (s ^ e) d := Nat.Coprime.pow_left e (coprime_odd_of_dvd_four hsodd hd)
  have hM1 : (p ^ a) ^ 6 ∣ M := Nat.Coprime.dvd_of_dvd_mul_right hcopg ⟨FX, E1⟩
  have hM2 : s ^ e ∣ M := Nat.Coprime.dvd_of_dvd_mul_right hcopse ⟨FY, E2⟩
  have hcopqs : Nat.Coprime (s ^ e) ((p ^ a) ^ 6) := Nat.Coprime.pow e 6 hcopq_s.symm
  have hsFX : s ^ e ∣ FX := by
    have h1 : s ^ e ∣ (p ^ a) ^ 6 * FX := by
      rw [← E1]
      exact Dvd.dvd.mul_right hM2 g
    exact Nat.Coprime.dvd_of_dvd_mul_left hcopqs h1
  have hsle : s ^ e ≤ FX := Nat.le_of_dvd hFX0 hsFX
  have hsq : s < p ^ a := lt_of_pow_le_lt he hs1 (lt_of_le_of_lt hsle hFX)
  have hcopq6_se : Nat.Coprime ((p ^ a) ^ 6) (s ^ e) := Nat.Coprime.pow 6 e hcopq_s
  have hqY : (p ^ a) ^ 6 ∣ FY := by
    have h := Dvd.dvd.mul_right hM1 d
    rw [E2] at h
    exact Nat.Coprime.dvd_of_dvd_mul_left hcopq6_se h
  exact ⟨hqY, hsle, hsq⟩

theorem cross_ge5_B {M p s a g d FX : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs2 : 2 ≤ s) (hsodd : Odd s) (hps : ¬ p ∣ s) (hg : g ∣ 4) (hd : d ∣ 4)
    (hFX0 : 0 < FX) (hFX : FX < (p ^ a) ^ 9)
    (E1 : M * g = (p ^ a) ^ 6 * FX)
    (E2 : M * d = s ^ 9 * ((s ^ 2 - 1) * ((s ^ 4 - 1) * (s ^ 6 - 1)))) : False := by
  obtain ⟨x, hx⟩ : ∃ x, s ^ 2 = x + 1 :=
    ⟨s ^ 2 - 1, by have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨hx2, hx4, hx6, -, -⟩ := sq_facts hx
  have hx1 : 1 ≤ x := by nlinarith
  have E2' : M * d = s ^ 9 * (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3))) := by
    rw [E2, hx2, hx4, hx6]
    ring
  obtain ⟨hqY, -, hsq⟩ := cross_core hp hp5 (by omega) hsodd hps hg hd hFX0 hFX E1 E2' (by norm_num)
  obtain ⟨hb1, hb2, hb3, -, -, -⟩ := blk_bounds hs2 hx
  have hpowA : p ^ (a * 6) = (p ^ a) ^ 6 := by rw [← pow_mul]
  rw [← hpowA] at hqY
  rcases YS05NonIso.sf2 hp (nc_x3 hp hp5) hqY with h | h
  · rw [hpowA] at h
    have hle := Nat.le_of_dvd (pow_pos (by omega) 3) h
    exact lt_asymm hsq (lt_of_pow6 (lt_of_le_of_lt hle hb1))
  · rcases YS05NonIso.sf2 hp (nc_x2 hp) h with h' | h'
    · rw [hpowA] at h'
      have hle := Nat.le_of_dvd (by omega) h'
      exact lt_asymm hsq (lt_of_pow6 (lt_of_le_of_lt hle hb2))
    · rw [hpowA] at h'
      have hle := Nat.le_of_dvd (by positivity) h'
      exact lt_asymm hsq (lt_of_pow6 (lt_of_le_of_lt hle hb3))

theorem cross_ge5_D {M p s a g d FX : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs2 : 2 ≤ s) (hsodd : Odd s) (hps : ¬ p ∣ s) (hg : g ∣ 4) (hd : d ∣ 4)
    (hFX0 : 0 < FX) (hFX : FX < (p ^ a) ^ 9)
    (E1 : M * g = (p ^ a) ^ 6 * FX)
    (E2 : M * d = s ^ 12 * ((s ^ 4 - 1) * ((s ^ 2 - 1) * ((s ^ 4 - 1) * (s ^ 6 - 1))))) :
    False := by
  obtain ⟨x, hx⟩ : ∃ x, s ^ 2 = x + 1 :=
    ⟨s ^ 2 - 1, by have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨hx2, hx4, hx6, -, -⟩ := sq_facts hx
  have hx1 : 1 ≤ x := by nlinarith
  have E2' : M * d = s ^ 12 * (x ^ 4 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3))) := by
    rw [E2, hx2, hx4, hx6]
    ring
  obtain ⟨hqY, hsle, hsq⟩ := cross_core hp hp5 (by omega) hsodd hps hg hd hFX0 hFX E1 E2'
    (by norm_num)
  have hs12 : s ^ 12 < (p ^ a) ^ 9 := lt_of_le_of_lt hsle hFX
  obtain ⟨hb1, hb2, hb3, -, hb5, hb6⟩ := blk_bounds hs2 hx
  have hpowA : p ^ (a * 6) = (p ^ a) ^ 6 := by rw [← pow_mul]
  rw [← hpowA] at hqY
  rcases YS05NonIso.sf2 hp (nc_x4 hp hp5) hqY with h | h
  ·
    rw [hpowA] at h
    have hle := Nat.le_of_dvd (pow_pos (by omega) 4) h
    have hlt : (p ^ a) ^ 6 < s ^ 8 := lt_of_le_of_lt hle hb6
    have h9 : (p ^ a) ^ 9 < s ^ 12 := by
      have h2 : ((p ^ a) ^ 9) ^ 2 < (s ^ 12) ^ 2 := by
        rw [show ((p ^ a) ^ 9) ^ 2 = ((p ^ a) ^ 6) ^ 3 by ring,
          show (s ^ 12) ^ 2 = (s ^ 8) ^ 3 by ring]
        exact Nat.pow_lt_pow_left hlt (by norm_num)
      exact (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num)).1 h2
    exact lt_asymm hs12 h9
  · rcases YS05NonIso.sf2 hp (nc_x22 hp) h with h' | h'
    · rw [hpowA] at h'
      have hle := Nat.le_of_dvd (by positivity) h'
      exact lt_asymm hsq (lt_of_pow6 (lt_of_le_of_lt hle hb5))
    · rw [hpowA] at h'
      have hle := Nat.le_of_dvd (by positivity) h'
      exact lt_asymm hsq (lt_of_pow6 (lt_of_le_of_lt hle hb3))

theorem cross_ge5_D2 {M p s a g d FX : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs2 : 2 ≤ s) (hsodd : Odd s) (hps : ¬ p ∣ s) (hg : g ∣ 4) (hd : d ∣ 4)
    (hFX0 : 0 < FX) (hFX : FX < (p ^ a) ^ 9)
    (E1 : M * g = (p ^ a) ^ 6 * FX)
    (E2 : M * d = s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * ((s ^ 4 - 1) * (s ^ 6 - 1))))) :
    False := by
  obtain ⟨x, hx⟩ : ∃ x, s ^ 2 = x + 1 :=
    ⟨s ^ 2 - 1, by have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨hx2, hx4, hx6, hx41, -⟩ := sq_facts hx
  have hx1 : 1 ≤ x := by nlinarith
  have E2' : M * d = s ^ 12 * ((x * (x + 2) + 2) * (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3)))) := by
    rw [E2, hx41, hx2, hx4, hx6]
    ring
  obtain ⟨hqY, -, hsq⟩ := cross_core hp hp5 (by omega) hsodd hps hg hd hFX0 hFX E1 E2'
    (by norm_num)
  obtain ⟨hb1, hb2, hb3, hb4, -, -⟩ := blk_bounds hs2 hx
  have hb4' : x * (x + 2) + 2 < s ^ 6 := by
    rw [show x * (x + 2) + 2 = x ^ 2 + 2 * x + 2 by ring]
    exact hb4
  have hpowA : p ^ (a * 6) = (p ^ a) ^ 6 := by rw [← pow_mul]
  rw [← hpowA] at hqY
  rcases YS05NonIso.sf2 hp (nc_D2 hp hp5) hqY with h | h
  · rw [hpowA] at h
    have hle := Nat.le_of_dvd (by positivity) h
    exact lt_asymm hsq (lt_of_pow6 (lt_of_le_of_lt hle hb4'))
  · rcases YS05NonIso.sf2 hp (nc_x3 hp hp5) h with h' | h'
    · rw [hpowA] at h'
      have hle := Nat.le_of_dvd (pow_pos (by omega) 3) h'
      exact lt_asymm hsq (lt_of_pow6 (lt_of_le_of_lt hle hb1))
    · rcases YS05NonIso.sf2 hp (nc_x2 hp) h' with h'' | h''
      · rw [hpowA] at h''
        have hle := Nat.le_of_dvd (by omega) h''
        exact lt_asymm hsq (lt_of_pow6 (lt_of_le_of_lt hle hb2))
      · rw [hpowA] at h''
        have hle := Nat.le_of_dvd (by positivity) h''
        exact lt_asymm hsq (lt_of_pow6 (lt_of_le_of_lt hle hb3))

end CFSG.LocalAnalysis.GLTheoremA.SFM11
