module

public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG

namespace C1

theorem eq_of_pow_mul_eq {p a b N N' : ℕ} (hp : p.Prime) (hN : ¬ p ∣ N) (hN' : ¬ p ∣ N')
    (h : p ^ a * N = p ^ b * N') : a = b ∧ N = N' := by
  have hN0 : N ≠ 0 := fun h0 => hN (h0 ▸ dvd_zero p)
  have hN'0 : N' ≠ 0 := fun h0 => hN' (h0 ▸ dvd_zero p)
  have hf : ∀ c M : ℕ, M ≠ 0 → ¬ p ∣ M → (p ^ c * M).factorization p = c := fun c M hM hpM => by
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hM, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpM,
      add_zero]
  have hab : a = b := by rw [← hf a N hN0 hN, ← hf b N' hN'0 hN', h]
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a) h⟩

theorem prod_Icc_two_four_sub (q : ℕ) :
    ∏ i ∈ Finset.Icc 2 4, (q ^ i - 1) = (q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)) := by
  rw [show Finset.Icc 2 4 = {2, 3, 4} from rfl]
  simp

theorem prod_Icc_two_four_twisted {q : ℕ} (hq : 1 ≤ q) :
    ∏ i ∈ Finset.Icc 2 4, (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat =
      (q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)) := by
  rw [show Finset.Icc 2 4 = {2, 3, 4} from rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have e2 : (((q : ℤ)) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    rw [show ((-1 : ℤ)) ^ 2 = 1 by norm_num, ← Nat.cast_pow]; omega
  have e3 : (((q : ℤ)) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    rw [show ((-1 : ℤ)) ^ 3 = -1 by norm_num, ← Nat.cast_pow]; omega
  have e4 : (((q : ℤ)) ^ 4 - (-1) ^ 4).toNat = q ^ 4 - 1 := by
    rw [show ((-1 : ℤ)) ^ 4 = 1 by norm_num, ← Nat.cast_pow]; omega
  rw [e2, e3, e4]

theorem not_dvd_pow_sub_one {p q i : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hq : 1 ≤ q) (hi : 1 ≤ i) :
    ¬ p ∣ q ^ i - 1 := by
  intro h
  have hqi : p ∣ q ^ i := dvd_pow hpq (by omega)
  have hq1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have h1 := Nat.dvd_sub hqi h
  rw [Nat.sub_sub_self hq1] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem not_dvd_pow_add_one {p q i : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hi : 1 ≤ i) :
    ¬ p ∣ q ^ i + 1 := by
  intro h
  have hqi : p ∣ q ^ i := dvd_pow hpq (by omega)
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hqi).mp h))

theorem pow_nine_lt {s : ℕ} (hs : 3 ≤ s) : s ^ 9 < ((s ^ 6) ^ 2 - 1) / 2 := by
  have h27 : 27 ≤ s ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ s ^ 3 := Nat.pow_le_pow_left hs 3
  have h9 : 1 ≤ s ^ 9 := Nat.one_le_pow _ _ (by omega)
  have e : (s ^ 6) ^ 2 = s ^ 3 * s ^ 9 := by ring
  rw [e, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by norm_num)]
  have h3 : 27 * s ^ 9 ≤ s ^ 3 * s ^ 9 := Nat.mul_le_mul_right _ h27
  omega

theorem psl_four_factor_lt {s : ℕ} (hs : 1 ≤ s) :
    (s ^ 2 - 1) * ((s ^ 3 - 1) * (s ^ 4 - 1)) < s ^ 9 := by
  have h1 : s ^ 2 - 1 < s ^ 2 := Nat.sub_lt (Nat.one_le_pow _ _ hs) one_pos
  have h2 : s ^ 3 - 1 < s ^ 3 := Nat.sub_lt (Nat.one_le_pow _ _ hs) one_pos
  have h3 : s ^ 4 - 1 < s ^ 4 := Nat.sub_lt (Nat.one_le_pow _ _ hs) one_pos
  calc (s ^ 2 - 1) * ((s ^ 3 - 1) * (s ^ 4 - 1)) < s ^ 2 * (s ^ 3 * s ^ 4) :=
        Nat.mul_lt_mul'' h1 (Nat.mul_lt_mul'' h2 h3)
    _ = s ^ 9 := by ring

theorem psu_four_factor_lt {s : ℕ} (hs : 1 ≤ s) :
    (s ^ 2 - 1) * ((s ^ 3 + 1) * (s ^ 4 - 1)) < 2 * s ^ 9 := by
  have h1 : s ^ 2 - 1 < s ^ 2 := Nat.sub_lt (Nat.one_le_pow _ _ hs) one_pos
  have h2 : s ^ 3 + 1 ≤ 2 * s ^ 3 := by have := Nat.one_le_pow 3 s hs; omega
  have h3 : s ^ 4 - 1 ≤ s ^ 4 := Nat.sub_le _ _
  calc (s ^ 2 - 1) * ((s ^ 3 + 1) * (s ^ 4 - 1)) < s ^ 2 * ((2 * s ^ 3) * s ^ 4) :=
        Nat.mul_lt_mul_of_lt_of_le h1 (Nat.mul_le_mul h2 h3)
          (Nat.mul_pos (by have := Nat.one_le_pow 3 s hs; omega) (Nat.one_le_pow _ _ hs))
    _ = 2 * s ^ 9 := by ring

theorem add_one_dvd_sq_sub_one (s : ℕ) : s + 1 ∣ s ^ 2 - 1 := by
  have h := Nat.sq_sub_sq s 1
  rw [one_pow] at h
  rw [h]
  exact dvd_mul_right _ _

theorem ordA_one_eq {q : ℕ} (hq : Odd q) : Open.ordA 1 q = q * ((q ^ 2 - 1) / 2) := by
  obtain ⟨m, hm⟩ := hq
  have hg2 : Nat.gcd (1 + 1) (q - 1) = 2 := by
    rw [hm, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 m)
  have h2d : 2 ∣ q ^ 2 - 1 := by
    have h := Nat.sq_sub_sq q 1
    rw [one_pow] at h
    rw [h, hm, Nat.add_sub_cancel]
    exact (dvd_mul_right 2 m).mul_left _
  unfold Open.ordA
  rw [hg2, show (1 * (1 + 1) / 2 : ℕ) = 1 from rfl, pow_one, show (1 + 1 : ℕ) = 2 from rfl,
    Finset.Icc_self, Finset.prod_singleton]
  exact Nat.mul_div_assoc q h2d

end C1

theorem not_lieModel_psl_two_of_four {Y : Type} [Group Y] {p a k : ℕ} (hp2 : p ≠ 2)
    (h2 : Blueprint.LieModel Y .PSL 2 p a)
    (h4 : Blueprint.LieModel Y .PSL 4 p k ∨ Blueprint.LieModel Y .PSU 4 p k) : False := by
  obtain ⟨⟨hp, ha, -⟩, -⟩ := GH74.statedClassicalModel_of_lieModel two_ne_zero h2
  have hpos : 0 < p := hp.pos
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have h3p : 3 ≤ p := by rcases hodd with ⟨m, hm⟩; have := hp.two_le; omega
  have hpq : p ∣ p ^ a := dvd_pow_self p (by omega)
  have hq1 : 1 ≤ p ^ a := Nat.one_le_pow _ _ hpos
  have hY2 : Nat.card Y = p ^ a * (((p ^ a) ^ 2 - 1) / 2) := by
    rw [GH74.card_of_lieModel_PSL two_ne_zero h2]
    exact C1.ordA_one_eq hodd.pow
  have h2d : 2 ∣ (p ^ a) ^ 2 - 1 := by
    have h := Nat.sq_sub_sq (p ^ a) 1
    rw [one_pow] at h
    obtain ⟨m, hm⟩ := (hodd.pow : Odd (p ^ a))
    rw [h, hm, Nat.add_sub_cancel]
    exact (dvd_mul_right 2 m).mul_left _
  have hu : ¬ p ∣ ((p ^ a) ^ 2 - 1) / 2 := fun h =>
    C1.not_dvd_pow_sub_one hp hpq hq1 one_le_two (h.trans (Nat.div_dvd_of_dvd h2d))
  have hcase : ∀ (P d : ℕ), d ∣ P → ¬ p ∣ P → Nat.card Y = (p ^ k) ^ 6 * (P / d) →
      P / d < (((p ^ k) ^ 6) ^ 2 - 1) / 2 → False := by
    intro P d hdP hpP hY4 hlt
    have hv : ¬ p ∣ P / d := fun h => hpP (h.trans (Nat.div_dvd_of_dvd hdP))
    have heq : p ^ a * (((p ^ a) ^ 2 - 1) / 2) = p ^ (6 * k) * (P / d) := by
      rw [← hY2, hY4, ← pow_mul, mul_comm k 6]
    obtain ⟨ha6, huv⟩ := C1.eq_of_pow_mul_eq hp hu hv heq
    have hqs : p ^ a = (p ^ k) ^ 6 := by rw [ha6, ← pow_mul, mul_comm k 6]
    rw [hqs] at huv
    omega
  rcases h4 with h4 | h4
  · obtain ⟨⟨-, hk, -⟩, -⟩ := GH74.statedClassicalModel_of_lieModel four_ne_zero h4
    have hps : p ∣ p ^ k := dvd_pow_self p (by omega)
    have hs1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hpos
    have hs3 : 3 ≤ p ^ k :=
      h3p.trans ((pow_one p).symm.le.trans (Nat.pow_le_pow_right hpos hk))
    have hdP : Nat.gcd 4 (p ^ k - 1) ∣
        ((p ^ k) ^ 2 - 1) * (((p ^ k) ^ 3 - 1) * ((p ^ k) ^ 4 - 1)) := by
      have h := Nat.sub_dvd_pow_sub_pow (p ^ k) 1 2
      rw [one_pow] at h
      exact (Nat.gcd_dvd_right 4 (p ^ k - 1)).trans (h.trans (dvd_mul_right _ _))
    have hpP : ¬ p ∣ ((p ^ k) ^ 2 - 1) * (((p ^ k) ^ 3 - 1) * ((p ^ k) ^ 4 - 1)) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      · exact C1.not_dvd_pow_sub_one hp hps hs1 (by norm_num) h1
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h1 | h1
      · exact C1.not_dvd_pow_sub_one hp hps hs1 (by norm_num) h1
      · exact C1.not_dvd_pow_sub_one hp hps hs1 (by norm_num) h1
    have hY4 : Nat.card Y = (p ^ k) ^ 6 *
        ((((p ^ k) ^ 2 - 1) * (((p ^ k) ^ 3 - 1) * ((p ^ k) ^ 4 - 1))) /
          Nat.gcd 4 (p ^ k - 1)) := by
      rw [GH74.card_of_lieModel_PSL four_ne_zero h4]
      unfold Open.ordA
      rw [show (4 - 1 : ℕ) = 3 from rfl, show (3 * (3 + 1) / 2 : ℕ) = 6 from rfl,
        show (3 + 1 : ℕ) = 4 from rfl, C1.prod_Icc_two_four_sub]
      exact Nat.mul_div_assoc _ hdP
    refine hcase _ _ hdP hpP hY4 ?_
    have h1 := C1.psl_four_factor_lt hs1
    have h2 := C1.pow_nine_lt hs3
    have h3 := Nat.div_le_self (((p ^ k) ^ 2 - 1) * (((p ^ k) ^ 3 - 1) * ((p ^ k) ^ 4 - 1)))
      (Nat.gcd 4 (p ^ k - 1))
    omega
  · obtain ⟨⟨-, hk, -⟩, -⟩ := GH74.statedClassicalModel_of_lieModel four_ne_zero h4
    have hps : p ∣ p ^ k := dvd_pow_self p (by omega)
    have hs1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hpos
    have hs3 : 3 ≤ p ^ k :=
      h3p.trans ((pow_one p).symm.le.trans (Nat.pow_le_pow_right hpos hk))
    have hdP : Nat.gcd 4 (p ^ k + 1) ∣
        ((p ^ k) ^ 2 - 1) * (((p ^ k) ^ 3 + 1) * ((p ^ k) ^ 4 - 1)) :=
      (Nat.gcd_dvd_right 4 (p ^ k + 1)).trans
        ((C1.add_one_dvd_sq_sub_one (p ^ k)).trans (dvd_mul_right _ _))
    have hd2 : 2 ≤ Nat.gcd 4 (p ^ k + 1) := by
      obtain ⟨m, hm⟩ := (hodd.pow : Odd (p ^ k))
      exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num))
        (Nat.dvd_gcd (by norm_num) ⟨m + 1, by omega⟩)
    have hpP : ¬ p ∣ ((p ^ k) ^ 2 - 1) * (((p ^ k) ^ 3 + 1) * ((p ^ k) ^ 4 - 1)) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      · exact C1.not_dvd_pow_sub_one hp hps hs1 (by norm_num) h1
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h1 | h1
      · exact C1.not_dvd_pow_add_one hp hps (by norm_num) h1
      · exact C1.not_dvd_pow_sub_one hp hps hs1 (by norm_num) h1
    have hY4 : Nat.card Y = (p ^ k) ^ 6 *
        ((((p ^ k) ^ 2 - 1) * (((p ^ k) ^ 3 + 1) * ((p ^ k) ^ 4 - 1))) /
          Nat.gcd 4 (p ^ k + 1)) := by
      rw [GH74.card_of_lieModel_PSU four_ne_zero hp2 h4]
      unfold Open.ordTwistedA
      rw [show (4 - 1 : ℕ) = 3 from rfl, show (3 * (3 + 1) / 2 : ℕ) = 6 from rfl,
        show (3 + 1 : ℕ) = 4 from rfl, C1.prod_Icc_two_four_twisted hs1]
      exact Nat.mul_div_assoc _ hdP
    refine hcase _ _ hdP hpP hY4 ?_
    have h1 := C1.psu_four_factor_lt hs1
    have h2 := C1.pow_nine_lt hs3
    have h3 : (((p ^ k) ^ 2 - 1) * (((p ^ k) ^ 3 + 1) * ((p ^ k) ^ 4 - 1))) /
        Nat.gcd 4 (p ^ k + 1) < (p ^ k) ^ 9 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc _ < 2 * (p ^ k) ^ 9 := h1
        _ ≤ Nat.gcd 4 (p ^ k + 1) * (p ^ k) ^ 9 := Nat.mul_le_mul_right _ hd2
        _ = (p ^ k) ^ 9 * Nat.gcd 4 (p ^ k + 1) := mul_comm _ _
    omega

end CFSG.ComponentClassification.HarrisLit
