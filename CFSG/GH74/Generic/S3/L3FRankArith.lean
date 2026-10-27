module

public import CFSG.GH74.Generic.S3.L3ClassC2T2

public section

namespace CFSG.GH74.Generic.S3.L3Ord

open CFSG.Open

theorem plus_factor {q : ℕ} (hq : 1 ≤ q) :
    (q ^ 2 - 1) * (q ^ 3 - 1) = (q - 1) * (q - 1) * (q + 1) * (q ^ 2 + q + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 : (a + 1) ^ 2 - 1 = a * (a + 2) := by
    rw [show (a + 1) ^ 2 = a * (a + 2) + 1 by ring]; simp
  have h3 : (a + 1) ^ 3 - 1 = a * ((a + 1) ^ 2 + (a + 1) + 1) := by
    rw [show (a + 1) ^ 3 = a * ((a + 1) ^ 2 + (a + 1) + 1) + 1 by ring]; simp
  rw [h2, h3]
  ring

theorem minus_factor {q : ℕ} (hq : 1 ≤ q) :
    (q ^ 2 - 1) * (q ^ 3 + 1) = (q - 1) * (q + 1) * (q + 1) * (q ^ 2 - q + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 : (a + 1) ^ 2 - 1 = a * (a + 2) := by
    rw [show (a + 1) ^ 2 = a * (a + 2) + 1 by ring]; simp
  have h3 : (a + 1) ^ 2 - (a + 1) + 1 = a * a + a + 1 := by
    rw [show (a + 1) ^ 2 = (a * a + a + 1) + a by ring]; omega
  rw [h2, h3]
  ring


theorem pow_dvd_plus_le {q r m : ℕ} (hq : 2 ≤ q) (hr : r.Prime) (hr2 : r ≠ 2)
    (h : r ^ m ∣ (q ^ 2 - 1) * (q ^ 3 - 1)) : r ^ m ≤ 3 * (q + 1) ^ 2 := by
  rw [plus_factor (by omega)] at h
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h ⊢
  have ha1 : 1 ≤ a := by omega
  have hgdef : (a + 1) ^ 2 + (a + 1) + 1 = (a + 2) * (a + 1) + 1 := by ring
  have hgdef' : (a + 1) ^ 2 + (a + 1) + 1 = a * (a + 3) + 3 := by ring
  set g := (a + 1) ^ 2 + (a + 1) + 1 with hg
  have hcop_bg : ∀ d : ℕ, d ∣ a + 2 → d ∣ g → d = 1 := by
    intro d hd1 hd2
    have h1 : d ∣ (a + 2) * (a + 1) := Dvd.dvd.mul_right hd1 _
    have h2 : d ∣ g - (a + 2) * (a + 1) := Nat.dvd_sub hd2 h1
    rw [hgdef] at h2
    simp at h2
    exact h2
  have hrnd : ∀ n : ℕ, ¬ r ∣ n → Nat.Coprime (r ^ m) n := fun n hn =>
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hr).2 hn)
  have hP : r ^ m ∣ (a + 2) * (a * a * g) := by
    have : a * a * (a + 1 + 1) * g = (a + 2) * (a * a * g) := by ring
    rw [this] at h; exact h
  have hP2 : r ^ m ∣ (a * a * g) * (a + 2) := by
    rw [mul_comm]; exact hP
  by_cases hbr : r ∣ a + 2
  · have hra : ¬ r ∣ a := fun h' => by
      have : r ∣ a + 2 - a := Nat.dvd_sub hbr h'
      rw [show a + 2 - a = 2 by omega] at this
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
    have hrg : ¬ r ∣ g := fun h' => hr.one_lt.ne' (hcop_bg r hbr h')
    have hn : ¬ r ∣ a * a * g := fun h' => by
      rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
      · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2 <;> exact hra h2
      · exact hrg h1
    have := (hrnd _ hn).dvd_of_dvd_mul_right hP
    have := Nat.le_of_dvd (by omega) this
    nlinarith
  · by_cases har : r ∣ a
    · have hn : Nat.Coprime (r ^ m) (a + 2) := hrnd _ hbr
      have h1 : r ^ m ∣ a * a * g := hn.dvd_of_dvd_mul_right hP2
      by_cases hrg : r ∣ g
      · have h3 : r ∣ 3 := by
          have h4 : r ∣ a * (a + 3) := Dvd.dvd.mul_right har _
          have h5 : r ∣ g - a * (a + 3) := Nat.dvd_sub hrg h4
          rw [hgdef'] at h5
          simpa using h5
        have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3
        subst hr3
        obtain ⟨c, hc⟩ := har
        have hgc : g = 3 * (3 * c ^ 2 + 3 * c + 1) := by
          rw [hg, show (a + 1) ^ 2 + (a + 1) + 1 = a ^ 2 + 3 * a + 3 by ring, hc]; ring
        have hu : Nat.Coprime (3 ^ m) (3 * c ^ 2 + 3 * c + 1) := by
          apply hrnd
          intro h6
          have : 3 ∣ 1 := by
            have h7 : 3 ∣ 3 * c ^ 2 + 3 * c := ⟨c ^ 2 + c, by ring⟩
            exact (Nat.dvd_add_right h7).1 h6
          omega
        have h8 : 3 ^ m ∣ (a * a * 3) * (3 * c ^ 2 + 3 * c + 1) := by
          rw [hgc] at h1
          have : a * a * (3 * (3 * c ^ 2 + 3 * c + 1)) = a * a * 3 * (3 * c ^ 2 + 3 * c + 1) := by ring
          rw [this] at h1; exact h1
        have h9 := hu.dvd_of_dvd_mul_right h8
        have := Nat.le_of_dvd (by positivity) h9
        nlinarith
      · have hn2 : ¬ r ∣ g := hrg
        have := (hrnd _ hn2).dvd_of_dvd_mul_right h1
        have := Nat.le_of_dvd (by positivity) this
        nlinarith
    · have hn : ¬ r ∣ a * a * (a + 2) := fun h' => by
        rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
        · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2 <;> exact har h2
        · exact hbr h1
      have h1 : r ^ m ∣ a * a * (a + 2) * g := by
        have : a * a * (a + 1 + 1) * g = a * a * (a + 2) * g := by ring
        rw [this] at h; exact h
      have := (hrnd _ hn).dvd_of_dvd_mul_left h1
      have := Nat.le_of_dvd (by positivity) this
      have hg3 : g ≤ 3 * (a + 1 + 1) ^ 2 := by rw [hg]; nlinarith
      omega


theorem pow_dvd_minus_le {q r m : ℕ} (hq : 2 ≤ q) (hr : r.Prime) (hr2 : r ≠ 2)
    (h : r ^ m ∣ (q ^ 2 - 1) * (q ^ 3 + 1)) : r ^ m ≤ 3 * (q + 1) ^ 2 := by
  rw [minus_factor (by omega)] at h
  obtain ⟨c, rfl⟩ : ∃ c, q = c + 2 := ⟨q - 2, by omega⟩
  have hq1 : c + 2 - 1 = c + 1 := by omega
  have hg' : (c + 2) ^ 2 - (c + 2) + 1 = c ^ 2 + 3 * c + 3 := by
    rw [show (c + 2) ^ 2 = (c ^ 2 + 3 * c + 3) + (c + 2) - 1 by ring_nf; omega]
    omega
  rw [hq1, hg'] at h
  set g := c ^ 2 + 3 * c + 3 with hg
  have hgdef : g = (c + 1) * (c + 2) + 1 := by rw [hg]; ring
  have hgdef' : g = (c + 3) * c + 3 := by rw [hg]; ring
  have hcop_ag : ∀ d : ℕ, d ∣ c + 1 → d ∣ g → d = 1 := by
    intro d hd1 hd2
    have h1 : d ∣ (c + 1) * (c + 2) := Dvd.dvd.mul_right hd1 _
    have h2 : d ∣ g - (c + 1) * (c + 2) := Nat.dvd_sub hd2 h1
    rw [hgdef] at h2
    simp at h2
    exact h2
  have hrnd : ∀ n : ℕ, ¬ r ∣ n → Nat.Coprime (r ^ m) n := fun n hn =>
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hr).2 hn)
  by_cases har : r ∣ c + 1
  ·
    have hrb : ¬ r ∣ c + 2 + 1 := fun h' => by
      have : r ∣ c + 2 + 1 - (c + 1) := Nat.dvd_sub h' har
      rw [show c + 2 + 1 - (c + 1) = 2 by omega] at this
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
    have hrg : ¬ r ∣ g := fun h' => hr.one_lt.ne' (hcop_ag r har h')
    have hn : ¬ r ∣ (c + 2 + 1) * (c + 2 + 1) * g := fun h' => by
      rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
      · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2 <;> exact hrb h2
      · exact hrg h1
    have h1 : r ^ m ∣ (c + 1) * ((c + 2 + 1) * (c + 2 + 1) * g) := by
      have : (c + 1) * (c + 2 + 1) * (c + 2 + 1) * g =
          (c + 1) * ((c + 2 + 1) * (c + 2 + 1) * g) := by ring
      rw [this] at h; exact h
    have := (hrnd _ hn).dvd_of_dvd_mul_right h1
    have := Nat.le_of_dvd (by omega) this
    nlinarith
  · by_cases hbr : r ∣ c + 3
    ·
      have hbr' : r ∣ c + 2 + 1 := hbr
      have hb2 : (c + 2 + 1) = c + 3 := by ring
      by_cases hrg : r ∣ g
      · have h3 : r ∣ 3 := by
          have h4 : r ∣ (c + 3) * c := Dvd.dvd.mul_right hbr _
          have h5 : r ∣ g - (c + 3) * c := Nat.dvd_sub hrg h4
          rw [hgdef'] at h5
          simpa using h5
        have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3
        subst hr3
        obtain ⟨e, he⟩ := hbr
        obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
        have hcf : c = 3 * f := by omega
        subst hcf
        have hgc : g = 3 * (3 * f * (f + 1) + 1) := by
          rw [hg]; ring
        have hu : Nat.Coprime (3 ^ m) ((3 * f + 1) * (3 * f * (f + 1) + 1)) := by
          apply hrnd
          intro h6
          rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h6 with h7 | h7
          · exact har h7
          · have : 3 ∣ 1 := by
              have h8 : 3 ∣ 3 * f * (f + 1) := ⟨f * (f + 1), by ring⟩
              exact (Nat.dvd_add_right h8).1 h7
            omega
        have h8 : 3 ^ m ∣ (27 * (f + 1) ^ 2) * ((3 * f + 1) * (3 * f * (f + 1) + 1)) := by
          rw [hgc] at h
          have : (3 * f + 1) * (3 * f + 2 + 1) * (3 * f + 2 + 1) * (3 * (3 * f * (f + 1) + 1)) =
              (27 * (f + 1) ^ 2) * ((3 * f + 1) * (3 * f * (f + 1) + 1)) := by ring
          rw [this] at h; exact h
        have h9 := hu.dvd_of_dvd_mul_right h8
        have := Nat.le_of_dvd (by positivity) h9
        nlinarith
      · have hn : ¬ r ∣ (c + 1) * g := fun h' => by
          rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
          · exact har h1
          · exact hrg h1
        have h1 : r ^ m ∣ ((c + 1) * g) * ((c + 2 + 1) * (c + 2 + 1)) := by
          have : (c + 1) * (c + 2 + 1) * (c + 2 + 1) * g =
              ((c + 1) * g) * ((c + 2 + 1) * (c + 2 + 1)) := by ring
          rw [this] at h; exact h
        have := (hrnd _ hn).dvd_of_dvd_mul_left h1
        have := Nat.le_of_dvd (by positivity) this
        nlinarith
    · have hbr' : ¬ r ∣ c + 2 + 1 := hbr
      have hn : ¬ r ∣ (c + 1) * (c + 2 + 1) * (c + 2 + 1) := fun h' => by
        rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
        · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
          · exact har h2
          · exact hbr' h2
        · exact hbr' h1
      have := (hrnd _ hn).dvd_of_dvd_mul_left h
      have := Nat.le_of_dvd (by positivity) this
      nlinarith


theorem pow_dvd_plus_le_two {q m : ℕ} (hq : Odd q) (hq3 : 3 ≤ q)
    (h : 2 ^ m ∣ (q ^ 2 - 1) * (q ^ 3 - 1)) : 2 ^ m ≤ 3 * (q + 1) ^ 2 := by
  rw [plus_factor (by omega)] at h
  obtain ⟨k, rfl⟩ := hq
  simp only [Nat.add_sub_cancel] at h
  have hk : 1 ≤ k := by omega
  have hgodd : Odd ((2 * k + 1) ^ 2 + (2 * k + 1) + 1) := by
    refine ⟨2 * k ^ 2 + 3 * k + 1, by ring⟩
  have hcg : Nat.Coprime (2 ^ m) ((2 * k + 1) ^ 2 + (2 * k + 1) + 1) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hgodd)
  have h1 : 2 ^ m ∣ 2 * k * (2 * k) * (2 * k + 1 + 1) := by
    have h' : 2 ^ m ∣ (2 * k * (2 * k) * (2 * k + 1 + 1)) * ((2 * k + 1) ^ 2 + (2 * k + 1) + 1) := by
      have : 2 * k * (2 * k) * (2 * k + 1 + 1) * ((2 * k + 1) ^ 2 + (2 * k + 1) + 1) =
          2 * k * (2 * k) * (2 * k + 1 + 1) * ((2 * k + 1) ^ 2 + (2 * k + 1) + 1) := rfl
      simpa [mul_assoc] using h
    exact hcg.dvd_of_dvd_mul_right h'
  rcases Nat.even_or_odd k with hke | hko
  ·
    have hk1 : Odd (k + 1) := hke.add_one
    have h2 : 2 ^ m ∣ (2 * (2 * k * (2 * k))) * (k + 1) := by
      have : 2 * k * (2 * k) * (2 * k + 1 + 1) = (2 * (2 * k * (2 * k))) * (k + 1) := by ring
      rw [this] at h1; exact h1
    have hc : Nat.Coprime (2 ^ m) (k + 1) := Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hk1)
    have h3 := hc.dvd_of_dvd_mul_right h2
    have := Nat.le_of_dvd (by positivity) h3
    nlinarith
  ·
    have h2 : 2 ^ m ∣ (4 * (2 * k + 1 + 1)) * (k * k) := by
      have : 2 * k * (2 * k) * (2 * k + 1 + 1) = (4 * (2 * k + 1 + 1)) * (k * k) := by ring
      rw [this] at h1; exact h1
    have hc : Nat.Coprime (2 ^ m) (k * k) :=
      Nat.Coprime.pow_left m (Nat.coprime_two_left.2 (hko.mul hko))
    have h3 := hc.dvd_of_dvd_mul_right h2
    have := Nat.le_of_dvd (by positivity) h3
    nlinarith


theorem pow_dvd_minus_le_two {q m : ℕ} (hq : Odd q) (hq3 : 3 ≤ q)
    (h : 2 ^ m ∣ (q ^ 2 - 1) * (q ^ 3 + 1)) : 2 ^ m ≤ 3 * (q + 1) ^ 2 := by
  rw [minus_factor (by omega)] at h
  obtain ⟨k, rfl⟩ := hq
  simp only [Nat.add_sub_cancel] at h
  have hk : 1 ≤ k := by omega
  have hgodd : Odd ((2 * k + 1) ^ 2 - (2 * k + 1) + 1) := by
    refine ⟨2 * k ^ 2 + k, ?_⟩
    have : (2 * k + 1) ^ 2 - (2 * k + 1) + 1 = 4 * k ^ 2 + 2 * k + 1 := by
      rw [show (2 * k + 1) ^ 2 = (4 * k ^ 2 + 2 * k + 1) + (2 * k + 1) - 1 by ring_nf; omega]
      omega
    rw [this]; ring
  have hcg : Nat.Coprime (2 ^ m) ((2 * k + 1) ^ 2 - (2 * k + 1) + 1) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hgodd)
  have h1 : 2 ^ m ∣ 2 * k * (2 * k + 1 + 1) * (2 * k + 1 + 1) := by
    exact hcg.dvd_of_dvd_mul_right (by simpa [mul_assoc] using h)
  rcases Nat.even_or_odd k with hke | hko
  · have hk1 : Odd (k + 1) := hke.add_one
    have h2 : 2 ^ m ∣ (8 * k) * ((k + 1) * (k + 1)) := by
      have : 2 * k * (2 * k + 1 + 1) * (2 * k + 1 + 1) = (8 * k) * ((k + 1) * (k + 1)) := by ring
      rw [this] at h1; exact h1
    have hc : Nat.Coprime (2 ^ m) ((k + 1) * (k + 1)) :=
      Nat.Coprime.pow_left m (Nat.coprime_two_left.2 (hk1.mul hk1))
    have h3 := hc.dvd_of_dvd_mul_right h2
    have := Nat.le_of_dvd (by positivity) h3
    nlinarith
  · have h2 : 2 ^ m ∣ (8 * ((k + 1) * (k + 1))) * k := by
      have : 2 * k * (2 * k + 1 + 1) * (2 * k + 1 + 1) = (8 * ((k + 1) * (k + 1))) * k := by ring
      rw [this] at h1; exact h1
    have hc : Nat.Coprime (2 ^ m) k := Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hko)
    have h3 := hc.dvd_of_dvd_mul_right h2
    have := Nat.le_of_dvd (by positivity) h3
    nlinarith


theorem not_dvd_ordA_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    ¬ p ^ (3 * f + 1) ∣ ordA 2 (p ^ f) := by
  intro h
  have hm := ordA_two_mul (p ^ f) (Nat.one_le_pow _ _ hp.pos)
  have h1 : p ^ (3 * f + 1) ∣ p ^ (3 * f) * ((p ^ (2 * f) - 1) * (p ^ (3 * f) - 1)) := by
    have : (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) =
        p ^ (3 * f) * ((p ^ (2 * f) - 1) * (p ^ (3 * f) - 1)) := by
      rw [← pow_mul, ← pow_mul, mul_comm f 3, mul_comm f 2]
    rw [← this, ← hm]
    exact Dvd.dvd.mul_right h _
  rw [pow_succ] at h1
  have h2 : p ∣ (p ^ (2 * f) - 1) * (p ^ (3 * f) - 1) := by
    have := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h1
    exact this
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
  · have h4 : p ∣ p ^ (2 * f) := dvd_pow_self p (by omega)
    have : p ∣ 1 := by
      have h5 : p ∣ p ^ (2 * f) - (p ^ (2 * f) - 1) := Nat.dvd_sub h4 h3
      rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h5
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  · have h4 : p ∣ p ^ (3 * f) := dvd_pow_self p (by omega)
    have : p ∣ 1 := by
      have h5 : p ∣ p ^ (3 * f) - (p ^ (3 * f) - 1) := Nat.dvd_sub h4 h3
      rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h5
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)


theorem not_dvd_ordTwistedA_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    ¬ p ^ (3 * f + 1) ∣ ordTwistedA 2 (p ^ f) := by
  intro h
  have hm := ordTwistedA_two_mul (p ^ f)
  have h1 : p ^ (3 * f + 1) ∣ p ^ (3 * f) * ((p ^ (2 * f) - 1) * (p ^ (3 * f) + 1)) := by
    have : (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) =
        p ^ (3 * f) * ((p ^ (2 * f) - 1) * (p ^ (3 * f) + 1)) := by
      rw [← pow_mul, ← pow_mul, mul_comm f 3, mul_comm f 2]
    rw [← this, ← hm]
    exact Dvd.dvd.mul_right h _
  rw [pow_succ] at h1
  have h2 : p ∣ (p ^ (2 * f) - 1) * (p ^ (3 * f) + 1) := by
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h1
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
  · have h4 : p ∣ p ^ (2 * f) := dvd_pow_self p (by omega)
    have : p ∣ 1 := by
      have h5 : p ∣ p ^ (2 * f) - (p ^ (2 * f) - 1) := Nat.dvd_sub h4 h3
      rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h5
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  · have h4 : p ∣ p ^ (3 * f) := dvd_pow_self p (by omega)
    have : p ∣ 1 := (Nat.dvd_add_right h4).1 h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)

theorem qpow_le_a2 {p f N p' f' k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hN : N = ordA 2 (p ^ f) ∨ N = ordTwistedA 2 (p ^ f)) (hp' : p'.Prime)
    (h : (p' ^ f') ^ k ∣ N) : (p' ^ f') ^ k ≤ (p ^ f) ^ 3 := by
  have hq3 : 3 * (p ^ f + 1) ^ 2 ≤ (p ^ f) ^ 3 := by
    obtain ⟨c, hc⟩ : ∃ c, p ^ f = c + 5 := ⟨p ^ f - 5, by omega⟩
    rw [hc]; nlinarith [sq_nonneg c, Nat.zero_le c]
  rw [← pow_mul] at h ⊢
  by_cases hpp : p' = p
  · subst hpp
    by_contra hlt
    have hlt' : p' ^ (3 * f) < p' ^ (f' * k) := by
      have : (p' ^ f) ^ 3 = p' ^ (3 * f) := by rw [← pow_mul, mul_comm]
      rw [← this]; exact not_le.1 hlt
    have hle : 3 * f + 1 ≤ f' * k := by
      have := (Nat.pow_lt_pow_iff_right hp'.one_lt).1 hlt'
      omega
    have hd : p' ^ (3 * f + 1) ∣ N := (pow_dvd_pow p' hle).trans h
    rcases hN with rfl | rfl
    · exact not_dvd_ordA_two hp' hf hd
    · exact not_dvd_ordTwistedA_two hp' hf hd
  · have hcop : Nat.Coprime (p' ^ (f' * k)) ((p ^ f) ^ 3) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.pow_right 3 (Nat.Coprime.pow_right f
        ((Nat.coprime_primes hp' hp).2 hpp)))
    have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hq2 : 2 ≤ p ^ f := by omega
    have hq3' : 3 ≤ p ^ f := by omega
    rcases hN with rfl | rfl
    · have hm := ordA_two_mul (p ^ f) (by omega)
      have h1 : p' ^ (f' * k) ∣ (p ^ f) ^ 3 * ((((p ^ f) ^ 2 - 1)) * ((p ^ f) ^ 3 - 1)) := by
        rw [← hm]; exact (h.trans (Dvd.intro _ rfl))
      have h2 := hcop.dvd_of_dvd_mul_left h1
      by_cases hp'2 : p' = 2
      · subst hp'2
        have := pow_dvd_plus_le_two hqodd hq3' h2
        omega
      · have := pow_dvd_plus_le hq2 hp' hp'2 h2
        omega
    · have hm := ordTwistedA_two_mul (p ^ f)
      have h1 : p' ^ (f' * k) ∣ (p ^ f) ^ 3 * ((((p ^ f) ^ 2 - 1)) * ((p ^ f) ^ 3 + 1)) := by
        rw [← hm]; exact (h.trans (Dvd.intro _ rfl))
      have h2 := hcop.dvd_of_dvd_mul_left h1
      by_cases hp'2 : p' = 2
      · subst hp'2
        have := pow_dvd_minus_le_two hqodd hq3' h2
        omega
      · have := pow_dvd_minus_le hq2 hp' hp'2 h2
        omega



end CFSG.GH74.Generic.S3.L3Ord
