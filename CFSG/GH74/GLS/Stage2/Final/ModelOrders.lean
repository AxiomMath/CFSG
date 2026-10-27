module

public import CFSG.GH74.GLS.Stage2.Final.ModelArith
public import CFSG.ClassicalInvolution.Orders.Symplectic
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelArith

open CFSG.Assembly.LowTwoRank CFSG.Open

theorem field_card_prime_pow (F : Type) [Field F] [Finite F] :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ Nat.card F = p ^ f ∧ CharP F p := by
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  exact ⟨ringChar F, n, hp, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn, ringChar.charP F⟩

theorem card_psl4 {K : Type} [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 4 K)) = ordA 3 (Nat.card K) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num)]
  rfl

theorem card_psu4 {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedProj (StatedSU 4 (p ^ f) K)) = ordTwistedA 3 (p ^ f) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (by norm_num)]
  rfl

theorem card_psp4_mul {F : Type} [Field F] [Finite F] :
    ∃ e : ℕ, 1 ≤ e ∧ e * Nat.card (StatedProj (StatedSp 2 F)) =
      Nat.card F ^ 4 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) := by
  obtain ⟨p, f, hp, hf, hF, hc⟩ := field_card_prime_pow F
  by_cases h2 : p = 2
  · subst h2
    refine ⟨1, le_refl _, ?_⟩
    rw [one_mul, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo 2]
    have e : (∏ j ∈ Finset.Icc 1 2, (Nat.card F ^ (2 * j) - 1)) =
        (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1) := by
      have e : Finset.Icc 1 2 = {1, 2} := by decide
      rw [e]; simp
    rw [e]; norm_num
  · refine ⟨2, by norm_num, ?_⟩
    have h := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero (n := 2)
      (CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp h2 hF) (by norm_num)
    have e : (∏ j ∈ Finset.Icc 1 2, (Nat.card F ^ (2 * j) - 1)) =
        (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1) := by
      have e : Finset.Icc 1 2 = {1, 2} := by decide
      rw [e]; simp
    rw [e] at h
    rw [mul_comm]
    simpa using h

theorem card_psp4_lt_card_psl4 {F F' : Type} [Field F] [Finite F] [Field F'] [Finite F']
    (h : Nat.card F = Nat.card F') :
    Nat.card (StatedProj (StatedSp 2 F)) < Nat.card (StatedProj (StatedSL 4 F')) := by
  obtain ⟨e, he, h1⟩ := card_psp4_mul (F := F)
  obtain ⟨p, f, hp, hf, hF, -⟩ := field_card_prime_pow F
  have hq : 2 ≤ Nat.card F := by
    rw [hF]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  rw [card_psl4, ← h]
  exact lt_of_orders_L hq (Nat.gcd_le_left _ (by norm_num)) he h1
    (gcd_mul_ordA_three (q := Nat.card F))

theorem card_psp4_lt_card_psu4 {F F' : Type} [Field F] [Finite F] [Field F'] [Finite F']
    {q : ℕ} (hF : Nat.card F = q) (hF' : Nat.card F' = q ^ 2) :
    Nat.card (StatedProj (StatedSp 2 F)) < Nat.card (StatedProj (StatedSU 4 q F')) := by
  obtain ⟨e, he, h1⟩ := card_psp4_mul (F := F)
  obtain ⟨p, f, hp, hf, hF0, -⟩ := field_card_prime_pow F
  rw [hF] at hF0 h1
  have hq : 2 ≤ q := by
    rw [hF0]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hF'' : Nat.card F' = (p ^ f) ^ 2 := by rw [hF', hF0]
  have hcard := card_psu4 hp hf hF''
  rw [← hF0] at hcard
  rw [hcard]
  exact lt_of_orders_U hq (Nat.gcd_le_left _ (by norm_num)) he h1
    (gcd_mul_ordTwistedA_three (q := q))

theorem card_psp4_ne_card_psl4 {F F' : Type} [Field F] [Finite F] [Field F'] [Finite F']
    {p p' f f' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp' : p'.Prime) (hp'2 : p' ≠ 2) (hf : 1 ≤ f)
    (hf' : 1 ≤ f') (hF : Nat.card F = p ^ f) (hF' : Nat.card F' = p' ^ f') :
    Nat.card (StatedProj (StatedSp 2 F)) ≠ Nat.card (StatedProj (StatedSL 4 F')) := by
  intro h
  have hN := CFSG.ClassicalInvolution.card_statedProj_statedSp_eq_ordBC (n := 2) hp hp2 hF
    (by norm_num)
  have hM : Nat.card (StatedProj (StatedSL 4 F')) = ordA 3 (p' ^ f') := by
    rw [card_psl4, hF']
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hodd' : Odd (p' ^ f') := (hp'.odd_of_ne_two hp'2).pow
  have h1 := two_mul_ordBC_two hodd
  have h2 := gcd_mul_ordA_three (q := p' ^ f')
  rw [h, hM] at hN
  have hd2 : 2 ≤ Nat.gcd 4 (p' ^ f' - 1) := by
    refine Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.dvd_gcd (by norm_num) ?_)
    rcases hodd' with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  exact not_eq_L hp hp2 hp' hp'2 hf hf' (Nat.gcd_dvd_left _ _) hd2 (N := ordA 3 (p' ^ f'))
    (by rw [hN]; exact h1) h2

theorem card_psp4_ne_card_psu4 {F F' : Type} [Field F] [Finite F] [Field F']
    {p p' f f' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp' : p'.Prime) (hp'2 : p' ≠ 2) (hf : 1 ≤ f)
    (hf' : 1 ≤ f') (hF : Nat.card F = p ^ f) (hF' : Nat.card F' = (p' ^ f') ^ 2) :
    Nat.card (StatedProj (StatedSp 2 F)) ≠ Nat.card (StatedProj (StatedSU 4 (p' ^ f') F')) := by
  intro h
  have hN := CFSG.ClassicalInvolution.card_statedProj_statedSp_eq_ordBC (n := 2) hp hp2 hF
    (by norm_num)
  have hM := card_psu4 hp' hf' hF'
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hodd' : Odd (p' ^ f') := (hp'.odd_of_ne_two hp'2).pow
  have h1 := two_mul_ordBC_two hodd
  have h2 := gcd_mul_ordTwistedA_three (q := p' ^ f')
  rw [h, hM] at hN
  have hd2 : 2 ≤ Nat.gcd 4 (p' ^ f' + 1) := by
    refine Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.dvd_gcd (by norm_num) ?_)
    rcases hodd' with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  exact not_eq_U hp hp2 hp' hp'2 hf hf' (Nat.gcd_dvd_left _ _) hd2
    (N := ordTwistedA 3 (p' ^ f')) (by rw [hN]; exact h1) h2

end CFSG.GH74.GLS.Stage2.Final.ModelArith
