module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuReachRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FamilyArith

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Open CFSG.EvenSporadicStandard.Induction.Hyp

theorem not_psl2_of_pow_dvd {e N : ℕ} (he : 6 ≤ e) (hdvd : 2 ^ e ∣ N) (hle : 8 * N ≤ (2 ^ e) ^ 3)
    {q : ℕ} (hq : Odd q) (hq1 : 1 < q) : q * (q ^ 2 - 1) ≠ 2 * N := by
  intro h
  have hdvd' : 2 ^ (e + 1) ∣ q * (q ^ 2 - 1) := by
    rw [h, pow_succ']
    exact Nat.mul_dvd_mul_left 2 hdvd
  have hcop : Nat.Coprime (2 ^ (e + 1)) q := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hq)
  have h2 : 2 ^ (e + 1) ∣ q ^ 2 - 1 := hcop.dvd_of_dvd_mul_left hdvd'
  have h3 := two_pow_le_succ_of_dvd_sq_sub_one hq hq1 (by omega) h2
  set A : ℕ := 2 ^ e with hA
  have hA64 : 64 ≤ A := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hq3 : 3 ≤ q := by
    obtain ⟨m, rfl⟩ := hq
    omega
  have hsub : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; ring
  have hz : (q : ℤ) * ((q : ℤ) ^ 2 - 1) = 2 * (N : ℤ) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    simp only [Nat.cast_mul, hsub] at this
    push_cast at this
    linarith
  have hle' : 8 * (N : ℤ) ≤ (A : ℤ) ^ 3 := by exact_mod_cast hle
  have hP : (A : ℤ) - 1 ≤ q := by
    have : (A : ℤ) ≤ (q : ℤ) + 1 := by exact_mod_cast h3
    linarith
  have hAz : (64 : ℤ) ≤ A := by exact_mod_cast hA64
  have hP2 : (2 : ℤ) ≤ (A : ℤ) - 1 := by linarith
  have hmono := cube_sub_mono hP2 hP
  nlinarith [mul_pos (by linarith : (0 : ℤ) < A) (by linarith : (0 : ℤ) < A)]

theorem notExc_of_order_shape {X : Type} [Group X] {s b a N : ℕ} (hs : 3 ≤ s) (hb : 2 ≤ b)
    (hN : Nat.card X = N) (hdvd : (2 ^ s) ^ b ∣ N) (hle : N ≤ (2 ^ s) ^ a)
    (ha : a + 1 ≤ 3 * b) : NotExc X := by
  have hQ : 8 ≤ 2 ^ s := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have he : 6 ≤ s * b := by nlinarith
  have hA : (2 ^ s) ^ b = 2 ^ (s * b) := by rw [← pow_mul]
  rw [hA] at hdvd
  have h8 : 8 * N ≤ (2 ^ (s * b)) ^ 3 := by
    calc 8 * N ≤ 8 * (2 ^ s) ^ a := Nat.mul_le_mul_left 8 hle
      _ ≤ 2 ^ s * (2 ^ s) ^ a := Nat.mul_le_mul_right _ hQ
      _ = (2 ^ s) ^ (a + 1) := by rw [pow_succ']
      _ ≤ (2 ^ s) ^ (3 * b) := Nat.pow_le_pow_right (by positivity) ha
      _ = (2 ^ (s * b)) ^ 3 := by rw [← pow_mul, ← pow_mul]; ring_nf
  refine ⟨?_, ?_⟩
  · rintro ⟨e⟩
    have h := Nat.card_congr e.toEquiv
    rw [hN, card_alternatingGroup_seven] at h
    have h64 : 2 ^ 6 ∣ N := (Nat.pow_dvd_pow 2 he).trans hdvd
    rw [h] at h64
    omega
  · rintro ⟨p, f, hp, hp2, hm⟩
    have h := two_mul_card_of_lieModel_psl_two hp hp2 hm
    rw [hN] at h
    have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hf : 1 ≤ f := by
      rcases hm with ⟨-, hadm, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact hadm.2.1
      all_goals exact absurd h0 (by norm_num)
    have hq1 : 1 < p ^ f :=
      calc 1 < p := hp.one_lt
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    exact not_psl2_of_pow_dvd he hdvd h8 hq hq1 h.symm

theorem shape_aux {N Q R d b c : ℕ} (hN : N = Q ^ b * R / d) (hd : d ∣ R) (hR : R ≤ Q ^ c) :
    Q ^ b ∣ N ∧ N ≤ Q ^ (b + c) := by
  have h : N = Q ^ b * (R / d) := by rw [hN, Nat.mul_div_assoc _ hd]
  refine ⟨⟨R / d, h⟩, ?_⟩
  rw [h, pow_add]
  exact Nat.mul_le_mul_left _ ((Nat.div_le_self R d).trans hR)

theorem sub_one_dvd_sq_sub_one (Q : ℕ) : Q - 1 ∣ Q ^ 2 - 1 := Nat.sub_one_dvd_pow_sub_one Q 2

theorem succ_dvd_sq_sub_one (Q : ℕ) : Q + 1 ∣ Q ^ 2 - 1 := by
  have h := Nat.sq_sub_sq Q 1
  rw [one_pow] at h
  exact ⟨Q - 1, h⟩

theorem toNat_pow_add_one (Q i : ℕ) : ((Q : ℤ) ^ i + 1).toNat = Q ^ i + 1 := by
  rw [show (Q : ℤ) ^ i + 1 = ((Q ^ i + 1 : ℕ) : ℤ) by push_cast; ring]
  exact Int.toNat_natCast _

theorem toNat_pow_sub_one (Q i : ℕ) (hQ : 1 ≤ Q) : ((Q : ℤ) ^ i - 1).toNat = Q ^ i - 1 := by
  rw [show (Q : ℤ) ^ i - 1 = ((Q ^ i - 1 : ℕ) : ℤ) by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hQ)]; push_cast; ring]
  exact Int.toNat_natCast _

theorem ordA_three (Q : ℕ) : ordA 3 Q = Q ^ 6 * ((Q ^ 2 - 1) * ((Q ^ 3 - 1) * (Q ^ 4 - 1))) /
    Nat.gcd 4 (Q - 1) := by
  unfold ordA
  rw [show Finset.Icc 2 (3 + 1) = {2, 3, 4} by decide]
  simp [Finset.prod_insert]

theorem ordA_four (Q : ℕ) : ordA 4 Q =
    Q ^ 10 * ((Q ^ 2 - 1) * ((Q ^ 3 - 1) * ((Q ^ 4 - 1) * (Q ^ 5 - 1)))) / Nat.gcd 5 (Q - 1) := by
  unfold ordA
  rw [show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} by decide]
  simp [Finset.prod_insert]

theorem ordBC_two (Q : ℕ) :
    ordBC 2 Q = Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) / Nat.gcd 2 (Q - 1) := by
  unfold ordBC
  rw [show Finset.Icc 1 2 = {1, 2} by decide]
  simp [Finset.prod_insert]

theorem ordTwistedA_three (Q : ℕ) (hQ : 1 ≤ Q) : ordTwistedA 3 Q =
    Q ^ 6 * ((Q ^ 2 - 1) * ((Q ^ 3 + 1) * (Q ^ 4 - 1))) / Nat.gcd 4 (Q + 1) := by
  unfold ordTwistedA
  rw [show Finset.Icc 2 (3 + 1) = {2, 3, 4} by decide]
  simp [Finset.prod_insert, toNat_pow_add_one, toNat_pow_sub_one Q _ hQ]

theorem ordTwistedA_four (Q : ℕ) (hQ : 1 ≤ Q) : ordTwistedA 4 Q =
    Q ^ 10 * ((Q ^ 2 - 1) * ((Q ^ 3 + 1) * ((Q ^ 4 - 1) * (Q ^ 5 + 1)))) / Nat.gcd 5 (Q + 1) := by
  unfold ordTwistedA
  rw [show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} by decide]
  simp [Finset.prod_insert, toNat_pow_add_one, toNat_pow_sub_one Q _ hQ]

theorem notExc_suzuki {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : SuzukiModel X 2 (2 * n + 1)) : NotExc X := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  obtain rfl : a = n := by omega
  have hc : Nat.card X = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  set Q : ℕ := 2 ^ (2 * a + 1) with hQ
  have hQ8 : 8 ≤ Q := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine notExc_of_order_shape (s := 2 * a + 1) (b := 2) (a := 5) (by omega) le_rfl hc
    ⟨(Q - 1) * (Q ^ 2 + 1), by ring⟩ ?_ (by norm_num)
  have h1 : (Q - 1) * (Q ^ 2 + 1) ≤ Q ^ 3 := by
    zify [(by omega : 1 ≤ Q)]
    nlinarith
  calc Q ^ 2 * (Q - 1) * (Q ^ 2 + 1) = Q ^ 2 * ((Q - 1) * (Q ^ 2 + 1)) := by ring
    _ ≤ Q ^ 2 * Q ^ 3 := Nat.mul_le_mul_left _ h1
    _ = Q ^ 5 := by ring

theorem notExc_psp {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m) (h : LieModel X .PSp 2 2 m) :
    NotExc X := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).2.2.1 rfl
  have hd : Nat.gcd 2 ((2 ^ m) - 1) ∣ ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) :=
    ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one _)).trans (dvd_mul_right _ _)
  have hR : ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) ≤ (2 ^ m) ^ 6 := by
    calc ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) ≤ (2 ^ m) ^ 2 * (2 ^ m) ^ 4 :=
          Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = (2 ^ m) ^ 6 := by ring
  obtain ⟨hdvd, hle⟩ := shape_aux (ordBC_two (2 ^ m)) hd hR
  exact notExc_of_order_shape (s := m) (b := 4) (a := 10) hm (by norm_num) hc hdvd
    (by simpa using hle) (by norm_num)

theorem notExc_psl_four {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m) (h : LieModel X .PSL 4 2 m) :
    NotExc X := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).1 rfl
  have hd : Nat.gcd 4 ((2 ^ m) - 1) ∣ ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 - 1) *
      ((2 ^ m) ^ 4 - 1)) :=
    ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one _)).trans (dvd_mul_right _ _)
  have hR : ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 4 - 1)) ≤ (2 ^ m) ^ 9 := by
    calc ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 4 - 1))
        ≤ (2 ^ m) ^ 2 * ((2 ^ m) ^ 3 * (2 ^ m) ^ 4) :=
          Nat.mul_le_mul (Nat.sub_le _ _) (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
      _ = (2 ^ m) ^ 9 := by ring
  obtain ⟨hdvd, hle⟩ := shape_aux (ordA_three (2 ^ m)) hd hR
  exact notExc_of_order_shape (s := m) (b := 6) (a := 15) hm (by norm_num) hc hdvd
    (by simpa using hle) (by norm_num)

theorem notExc_psl_five {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m) (h : LieModel X .PSL 5 2 m) :
    NotExc X := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).1 rfl
  have hd : Nat.gcd 5 ((2 ^ m) - 1) ∣ ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 - 1) *
      (((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 5 - 1))) :=
    ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one _)).trans (dvd_mul_right _ _)
  have hR : ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 - 1) * (((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 5 - 1)))
      ≤ (2 ^ m) ^ 14 := by
    calc ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 - 1) * (((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 5 - 1)))
        ≤ (2 ^ m) ^ 2 * ((2 ^ m) ^ 3 * ((2 ^ m) ^ 4 * (2 ^ m) ^ 5)) :=
          Nat.mul_le_mul (Nat.sub_le _ _) (Nat.mul_le_mul (Nat.sub_le _ _)
            (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)))
      _ = (2 ^ m) ^ 14 := by ring
  obtain ⟨hdvd, hle⟩ := shape_aux (ordA_four (2 ^ m)) hd hR
  exact notExc_of_order_shape (s := m) (b := 10) (a := 24) hm (by norm_num) hc hdvd
    (by simpa using hle) (by norm_num)

theorem notExc_psu_four {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m) (h : LieModel X .PSU 4 2 m) :
    NotExc X := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).2.1 rfl
  have hQ1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hd : Nat.gcd 4 ((2 ^ m) + 1) ∣ ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 + 1) *
      ((2 ^ m) ^ 4 - 1)) :=
    ((Nat.gcd_dvd_right _ _).trans (succ_dvd_sq_sub_one _)).trans (dvd_mul_right _ _)
  have hQ : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 ^ m) ^ 3 + 1 ≤ (2 ^ m) ^ 4 := by
    calc (2 ^ m) ^ 3 + 1 ≤ (2 ^ m) ^ 3 * 2 := by
          have := Nat.one_le_pow 3 (2 ^ m) hQ1
          omega
      _ ≤ (2 ^ m) ^ 3 * (2 ^ m) := Nat.mul_le_mul_left _ hQ
      _ = (2 ^ m) ^ 4 := by ring
  have hR : ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1)) ≤ (2 ^ m) ^ 10 := by
    calc ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1))
        ≤ (2 ^ m) ^ 2 * ((2 ^ m) ^ 4 * (2 ^ m) ^ 4) :=
          Nat.mul_le_mul (Nat.sub_le _ _) (Nat.mul_le_mul h3 (Nat.sub_le _ _))
      _ = (2 ^ m) ^ 10 := by ring
  obtain ⟨hdvd, hle⟩ := shape_aux (ordTwistedA_three (2 ^ m) hQ1) hd hR
  exact notExc_of_order_shape (s := m) (b := 6) (a := 16) hm (by norm_num) hc hdvd
    (by simpa using hle) (by norm_num)

theorem notExc_psu_five {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m) (h : LieModel X .PSU 5 2 m) :
    NotExc X := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).2.1 rfl
  have hQ1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hd : Nat.gcd 5 ((2 ^ m) + 1) ∣ ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 + 1) *
      (((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 5 + 1))) :=
    ((Nat.gcd_dvd_right _ _).trans (succ_dvd_sq_sub_one _)).trans (dvd_mul_right _ _)
  have hQ : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 ^ m) ^ 3 + 1 ≤ (2 ^ m) ^ 4 := by
    calc (2 ^ m) ^ 3 + 1 ≤ (2 ^ m) ^ 3 * 2 := by
          have := Nat.one_le_pow 3 (2 ^ m) hQ1
          omega
      _ ≤ (2 ^ m) ^ 3 * (2 ^ m) := Nat.mul_le_mul_left _ hQ
      _ = (2 ^ m) ^ 4 := by ring
  have h5 : (2 ^ m) ^ 5 + 1 ≤ (2 ^ m) ^ 6 := by
    calc (2 ^ m) ^ 5 + 1 ≤ (2 ^ m) ^ 5 * 2 := by
          have := Nat.one_le_pow 5 (2 ^ m) hQ1
          omega
      _ ≤ (2 ^ m) ^ 5 * (2 ^ m) := Nat.mul_le_mul_left _ hQ
      _ = (2 ^ m) ^ 6 := by ring
  have hR : ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 + 1) * (((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 5 + 1)))
      ≤ (2 ^ m) ^ 16 := by
    calc ((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 + 1) * (((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 5 + 1)))
        ≤ (2 ^ m) ^ 2 * ((2 ^ m) ^ 4 * ((2 ^ m) ^ 4 * (2 ^ m) ^ 6)) :=
          Nat.mul_le_mul (Nat.sub_le _ _) (Nat.mul_le_mul h3
            (Nat.mul_le_mul (Nat.sub_le _ _) h5))
      _ = (2 ^ m) ^ 16 := by ring
  obtain ⟨hdvd, hle⟩ := shape_aux (ordTwistedA_four (2 ^ m) hQ1) hd hR
  exact notExc_of_order_shape (s := m) (b := 10) (a := 26) hm (by norm_num) hc hdvd
    (by simpa using hle) (by norm_num)

theorem notExc_of_thm54Types {X : Type} [Group X]
    (h : Sol78Thm54Types X) : NotExc X := by
  rcases h with ⟨n, hn, hX⟩ | ⟨m, hm, hX | hX | hX | hX | hX⟩
  · exact notExc_suzuki hn hX
  · exact notExc_psp hm hX
  · exact notExc_psu_four hm hX
  · exact notExc_psl_four hm hX
  · exact notExc_psu_five hm hX
  · exact notExc_psl_five hm hX

theorem ruFamilyFacts_of_cover_rank
    (hrank : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      Sol78Thm54Types (X ⧸ center X) → 3 ≤ CFSG.pRank 2 X) : RuFamilyFacts :=
  ⟨fun _ _ h => notExc_of_thm54Types h, hrank⟩

end CFSG.EvenSporadicStandard.Induction
