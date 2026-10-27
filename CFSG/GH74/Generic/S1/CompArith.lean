module

public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

open CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.Generic.S1

@[expose] def pslCard (q : ℕ) : ℕ := q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)

@[expose] def psuCard (q : ℕ) : ℕ := q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1)

@[expose] def l3Card (ε : ℤ) (q : ℕ) : ℕ := if ε = 1 then pslCard q else psuCard q

theorem card_stated_psl3 {K : Type} [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 3 K)) = pslCard (Nat.card K) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num)]
  unfold pslCard
  have : (∏ j ∈ Finset.Icc 2 3, (Nat.card K ^ j - 1)) = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
  rw [this]

theorem card_stated_psu3 {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) = psuCard (p ^ f) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (by norm_num)]
  unfold psuCard
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have h2 : ((((p ^ f : ℕ) : ℤ)) ^ 2 - (-1) ^ 2).toNat = (p ^ f) ^ 2 - 1 := by
    have : (((p ^ f : ℕ) : ℤ)) ^ 2 = (((p ^ f) ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [this]
    have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
    omega
  have h3 : ((((p ^ f : ℕ) : ℤ)) ^ 3 - (-1) ^ 3).toNat = (p ^ f) ^ 3 + 1 := by
    have : (((p ^ f : ℕ) : ℤ)) ^ 3 = (((p ^ f) ^ 3 : ℕ) : ℤ) := by push_cast; ring
    rw [this]
    omega
  rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num), h2, h3]

theorem gcd_dvd_sq_sub_one_left (q : ℕ) : Nat.gcd 3 (q - 1) ∣ q ^ 2 - 1 := by
  have h1 : q - 1 ∣ q ^ 2 - 1 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      refine ⟨k + 2, ?_⟩
      simp only [Nat.add_sub_cancel]
      exact Nat.sub_eq_of_eq_add (by ring)
  exact (Nat.gcd_dvd_right 3 (q - 1)).trans h1

theorem gcd_dvd_sq_sub_one_right (q : ℕ) : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 := by
  have h1 : q + 1 ∣ q ^ 2 - 1 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · refine ⟨q - 1, ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      exact Nat.sub_eq_of_eq_add (by ring)
  exact (Nat.gcd_dvd_right 3 (q + 1)).trans h1

theorem pslCard_mul (q : ℕ) :
    pslCard q * Nat.gcd 3 (q - 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  unfold pslCard
  apply Nat.div_mul_cancel
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (gcd_dvd_sq_sub_one_left q) _) _

theorem psuCard_mul (q : ℕ) :
    psuCard q * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  unfold psuCard
  apply Nat.div_mul_cancel
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (gcd_dvd_sq_sub_one_right q) _) _

theorem gcd_three_le (a : ℕ) : Nat.gcd 3 a ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 a)

theorem gcd_three_pos (a : ℕ) : 0 < Nat.gcd 3 a := Nat.gcd_pos_of_pos_left _ (by norm_num)

theorem big_prod {q : ℕ} (hq : 5 ≤ q) : 125 * (24 * 124) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h3 : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 25 ≤ q ^ 2 := by
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  exact Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))

theorem big_prod' {q : ℕ} (hq : 5 ≤ q) : 125 * (24 * 124) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h3 : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 25 ≤ q ^ 2 := by
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  exact Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))

theorem l3Card_large {ε : ℤ} {q : ℕ} (hq : 5 ≤ q) : 62400 < l3Card ε q := by
  unfold l3Card
  split_ifs
  · have h := pslCard_mul q
    have hg := gcd_three_le (q - 1)
    have hb := big_prod hq
    by_contra hle
    have : pslCard q * Nat.gcd 3 (q - 1) ≤ 62400 * 3 := Nat.mul_le_mul (by omega) hg
    omega
  · have h := psuCard_mul q
    have hg := gcd_three_le (q + 1)
    have hb := big_prod' hq
    by_contra hle
    have : psuCard q * Nat.gcd 3 (q + 1) ≤ 62400 * 3 := Nat.mul_le_mul (by omega) hg
    omega

theorem not_dvd_psl_psu {q : ℕ} (hq : 5 ≤ q) : ¬ pslCard q ∣ psuCard q := by
  rintro ⟨k, hk⟩
  have h1 := pslCard_mul q
  have h2 := psuCard_mul q
  set X := q ^ 3 * (q ^ 2 - 1) with hX
  have hXpos : 0 < X := by
    have : 25 ≤ q ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have : 0 < q ^ 3 := by positivity
    exact Nat.mul_pos this (by omega)
  have g1 := gcd_three_pos (q - 1)
  have g1le := gcd_three_le (q - 1)
  have g2 := gcd_three_pos (q + 1)
  have hx : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  set x := q ^ 3 with hxdef
  have key : (x + 1) * Nat.gcd 3 (q - 1) = (x - 1) * (k * Nat.gcd 3 (q + 1)) := by
    have e1 : X * (x - 1) = pslCard q * Nat.gcd 3 (q - 1) := by rw [h1, hX]; ring
    have e2 : X * (x + 1) = psuCard q * Nat.gcd 3 (q + 1) := by rw [h2, hX]; ring
    have e3 : X * ((x + 1) * Nat.gcd 3 (q - 1)) = X * ((x - 1) * (k * Nat.gcd 3 (q + 1))) := by
      calc X * ((x + 1) * Nat.gcd 3 (q - 1)) = (X * (x + 1)) * Nat.gcd 3 (q - 1) := by ring
        _ = (psuCard q * Nat.gcd 3 (q + 1)) * Nat.gcd 3 (q - 1) := by rw [e2]
        _ = (pslCard q * k * Nat.gcd 3 (q + 1)) * Nat.gcd 3 (q - 1) := by rw [hk]
        _ = (pslCard q * Nat.gcd 3 (q - 1)) * (k * Nat.gcd 3 (q + 1)) := by ring
        _ = (X * (x - 1)) * (k * Nat.gcd 3 (q + 1)) := by rw [e1]
        _ = X * ((x - 1) * (k * Nat.gcd 3 (q + 1))) := by ring
    exact Nat.eq_of_mul_eq_mul_left hXpos e3
  have hdvd : x - 1 ∣ (x + 1) * Nat.gcd 3 (q - 1) := ⟨k * Nat.gcd 3 (q + 1), key⟩
  have hsplit : (x + 1) * Nat.gcd 3 (q - 1) = (x - 1) * Nat.gcd 3 (q - 1) + 2 * Nat.gcd 3 (q - 1) := by
    obtain ⟨y, hy⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    rw [hy]
    simp only [Nat.add_sub_cancel]
    ring
  rw [hsplit] at hdvd
  have h2g : x - 1 ∣ 2 * Nat.gcd 3 (q - 1) :=
    (Nat.dvd_add_right (Dvd.intro _ rfl)).mp hdvd
  have := Nat.le_of_dvd (by omega) h2g
  omega

theorem not_dvd_psu_psl {q : ℕ} (hq : 5 ≤ q) : ¬ psuCard q ∣ pslCard q := by
  rintro ⟨k, hk⟩
  have h1 := pslCard_mul q
  have h2 := psuCard_mul q
  set X := q ^ 3 * (q ^ 2 - 1) with hX
  have hXpos : 0 < X := by
    have : 25 ≤ q ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have : 0 < q ^ 3 := by positivity
    exact Nat.mul_pos this (by omega)
  have g1 := gcd_three_pos (q - 1)
  have g2 := gcd_three_pos (q + 1)
  have g2le := gcd_three_le (q + 1)
  have hx : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  set x := q ^ 3 with hxdef
  have key : (x - 1) * Nat.gcd 3 (q + 1) = (x + 1) * (k * Nat.gcd 3 (q - 1)) := by
    have e1 : X * (x - 1) = pslCard q * Nat.gcd 3 (q - 1) := by rw [h1, hX]; ring
    have e2 : X * (x + 1) = psuCard q * Nat.gcd 3 (q + 1) := by rw [h2, hX]; ring
    have e3 : X * ((x - 1) * Nat.gcd 3 (q + 1)) = X * ((x + 1) * (k * Nat.gcd 3 (q - 1))) := by
      calc X * ((x - 1) * Nat.gcd 3 (q + 1)) = (X * (x - 1)) * Nat.gcd 3 (q + 1) := by ring
        _ = (pslCard q * Nat.gcd 3 (q - 1)) * Nat.gcd 3 (q + 1) := by rw [e1]
        _ = (psuCard q * k * Nat.gcd 3 (q - 1)) * Nat.gcd 3 (q + 1) := by rw [hk]
        _ = (psuCard q * Nat.gcd 3 (q + 1)) * (k * Nat.gcd 3 (q - 1)) := by ring
        _ = (X * (x + 1)) * (k * Nat.gcd 3 (q - 1)) := by rw [e2]
        _ = X * ((x + 1) * (k * Nat.gcd 3 (q - 1))) := by ring
    exact Nat.eq_of_mul_eq_mul_left hXpos e3
  have hdvd : x + 1 ∣ (x - 1) * Nat.gcd 3 (q + 1) := ⟨k * Nat.gcd 3 (q - 1), key⟩
  have hsplit : (x + 1) * Nat.gcd 3 (q + 1) = (x - 1) * Nat.gcd 3 (q + 1) + 2 * Nat.gcd 3 (q + 1) := by
    obtain ⟨y, hy⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    rw [hy]
    simp only [Nat.add_sub_cancel]
    ring
  have hdvd2 : x + 1 ∣ (x + 1) * Nat.gcd 3 (q + 1) := Dvd.intro _ rfl
  rw [hsplit] at hdvd2
  have h2g : x + 1 ∣ 2 * Nat.gcd 3 (q + 1) :=
    (Nat.dvd_add_right hdvd).mp hdvd2
  have := Nat.le_of_dvd (by omega) h2g
  omega

theorem eq_of_l3Card_dvd {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) {q : ℕ}
    (hq : 5 ≤ q) (h : l3Card ε q ∣ l3Card δ q) : ε = δ := by
  unfold l3Card at h
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
  · rfl
  · simp at h
    exact absurd h (not_dvd_psl_psu hq)
  · simp at h
    exact absurd h (not_dvd_psu_psl hq)
  · rfl


theorem l3Card_three_le (ε : ℤ) : l3Card ε 3 ≤ 6048 := by
  unfold l3Card
  split_ifs
  · unfold pslCard
    norm_num
  · unfold psuCard
    norm_num

end CFSG.GH74.Generic.S1
