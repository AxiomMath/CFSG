module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.QId

private theorem isOddPrimePower_of_odd {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' F
  have hpodd : Odd p := h.of_dvd_nat (by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p (by have := n.pos; omega))
  exact ⟨p, n, hp, hpodd, by have := n.pos; omega, by
    simpa only [Nat.card_eq_fintype_card] using hcard⟩

private theorem half_formula (m : ℕ) :
    (2 * m + 1) * ((2 * m + 1) ^ 2 - 1) / 2 = (2 * m + 1) * (2 * (m * (m + 1))) := by
  have h : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [h, show (2 * m + 1) * (4 * (m * (m + 1))) = 2 * ((2 * m + 1) * (2 * (m * (m + 1)))) by ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

private theorem order_lt {m m' : ℕ} (h : m < m') :
    (2 * m + 1) * (2 * (m * (m + 1))) < (2 * m' + 1) * (2 * (m' * (m' + 1))) :=
  Nat.mul_lt_mul'' (by omega)
    (by have := Nat.mul_lt_mul'' h (Nat.add_lt_add_right h 1); omega)

private theorem order_le {m m' : ℕ} (h : m ≤ m') :
    (2 * m + 1) * (2 * (m * (m + 1))) ≤ (2 * m' + 1) * (2 * (m' * (m' + 1))) := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (order_lt h).le

theorem card_isL2 {X : Type} [Group X] {q : ℕ} (hq : Odd q) (h : IVK.IsL2 X (fun r => r = q)) :
    Nat.card X = q * (q ^ 2 - 1) / 2 := by
  obtain ⟨F₀, _, _, hF, ⟨e⟩⟩ := h
  have hF' : Nat.card F₀ = q := hF
  have hpp := isOddPrimePower_of_odd (F := F₀) (hF' ▸ hq)
  rw [Nat.card_congr (e.toEquiv.trans (IVK.L2.equivPSL F₀).toEquiv),
    GorensteinWalter.psl2_card_formula F₀ hpp, hF']

theorem isL2_odd_unique {X : Type} [Group X] {q q' : ℕ} (hq : Odd q) (hq' : Odd q')
    (h : IVK.IsL2 X (fun r => r = q)) (h' : IVK.IsL2 X (fun r => r = q')) : q = q' := by
  have h1 := card_isL2 hq h
  have h2 := card_isL2 hq' h'
  obtain ⟨m, rfl⟩ := hq
  obtain ⟨m', rfl⟩ := hq'
  rw [half_formula] at h1 h2
  have hmm : m = m' := by
    rcases lt_trichotomy m m' with hlt | heq | hgt
    · exact absurd (h1.symm.trans h2) (order_lt hlt).ne
    · exact heq
    · exact absurd (h2.symm.trans h1) (order_lt hgt).ne
  rw [hmm]

theorem padicValNat_isL2_sq {X Y : Type} [Group X] [Group Y] {q : ℕ} (hq : Odd q)
    (hX : IVK.IsL2 X (fun r => r = q ^ 2)) (hY : IVK.IsL2 Y (fun r => r = q)) :
    padicValNat 2 (Nat.card X) = padicValNat 2 (Nat.card Y) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq1 : 1 < q := by
    obtain ⟨F₀, _, _, hF, _⟩ := hY
    have hF' : Nat.card F₀ = q := hF
    rw [← hF']
    exact Finite.one_lt_card
  have hcX := card_isL2 (hq.pow (n := 2)) hX
  have hcY := card_isL2 hq hY
  obtain ⟨m, rfl⟩ := hq
  have hsq : (2 * m + 1) ^ 2 = 2 * (2 * (m * (m + 1))) + 1 := by ring
  rw [hsq, half_formula] at hcX
  rw [half_formula] at hcY
  have hm : 1 ≤ m := by omega
  have hY0 : (2 * m + 1) * (2 * (m * (m + 1))) ≠ 0 := by positivity
  have hid : (2 * (2 * (m * (m + 1))) + 1) * (2 * (2 * (m * (m + 1)) * (2 * (m * (m + 1)) + 1))) =
      2 * ((2 * m + 1) * (2 * (m * (m + 1)))) * ((2 * m + 1) * (2 * (m * (m + 1)) + 1)) := by
    ring
  have hodd : ¬ 2 ∣ (2 * m + 1) * (2 * (m * (m + 1)) + 1) := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact Odd.mul ⟨m, rfl⟩ ⟨m * (m + 1), rfl⟩
  rw [hcX, hcY, hid, padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by norm_num) hY0, padicValNat.eq_zero_of_not_dvd hodd, padicValNat_self]
  omega

theorem eq_five_of_isL2_dvd_sixty {Y : Type} [Group Y] {q : ℕ} (hq : Odd q) (hq3 : 3 < q)
    (hY : IVK.IsL2 Y (fun r => r = q)) (hd : Nat.card Y ∣ 60) : q = 5 := by
  have hc := card_isL2 hq hY
  obtain ⟨m, rfl⟩ := hq
  rw [half_formula] at hc
  have hle : (2 * m + 1) * (2 * (m * (m + 1))) ≤ 60 := hc ▸ Nat.le_of_dvd (by norm_num) hd
  have hm3 : m < 3 := by
    by_contra hcon
    have := order_le (not_lt.mp hcon)
    norm_num at this
    omega
  have hm2 : 2 ≤ m := by omega
  omega

theorem padicValNat_isL2_five {Y : Type} [Group Y] (hY : IVK.IsL2 Y (fun r => r = 5)) :
    padicValNat 2 (Nat.card Y) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := card_isL2 (by decide : Odd 5) hY
  rw [hc, show 5 * (5 ^ 2 - 1) / 2 = 2 ^ 2 * 15 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem padicValNat_alternating_seven :
    padicValNat 2 (Nat.card (alternatingGroup (Fin 7))) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h7 : Nat.card (alternatingGroup (Fin 7)) = 2 ^ 3 * 315 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [h7, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

end CFSG.GH74.GLS.Stage2.Local.P27.QId
