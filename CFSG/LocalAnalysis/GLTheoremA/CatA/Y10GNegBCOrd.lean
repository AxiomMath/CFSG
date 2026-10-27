module

public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC

open CFSG.Open CFSG.Assembly CFSG.Timmesfeld.ClassicalOrders

theorem prod_icc_two_six {Q : ℕ} (hQ : 1 ≤ Q) :
    ∏ i ∈ Finset.Icc 2 6, (((Q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat =
      (Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1) * (Q ^ 5 + 1) * (Q ^ 6 - 1) := by
  have h : Finset.Icc 2 6 = {2, 3, 4, 5, 6} := by decide
  have e1 : ∀ i, ((Q : ℤ) ^ i).toNat = Q ^ i := fun i => by rw [← Nat.cast_pow, Int.toNat_natCast]
  have e2 : ∀ i, ((Q : ℤ) ^ i + 1).toNat = Q ^ i + 1 := fun i => by
    have : ((Q : ℤ) ^ i + 1) = ((Q ^ i + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [h]
  simp [Finset.prod_insert, e1, e2]
  ring


theorem odd_pred_of_even {n : ℕ} (hn : 2 ≤ n) (h : 2 ∣ n) : Odd (n - 1) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k - 1, by omega⟩

theorem odd_succ_of_even {n : ℕ} (h : 2 ∣ n) : Odd (n + 1) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by omega⟩

theorem card_psl_four_eq {E : Type} [Field E] [Finite E] (hE2 : 2 ∣ Nat.card E) (hE : 2 ≤ Nat.card E) :
    Nat.card (StatedProj (StatedSL 4 E)) =
      Nat.card E ^ 6 * ((Nat.card E ^ 2 - 1) * (Nat.card E ^ 3 - 1) * (Nat.card E ^ 4 - 1)) := by
  rw [card_statedProj_statedSL (K := E) (n := 4) (by norm_num)]
  have hg : Nat.gcd 4 (Nat.card E - 1) = 1 := by
    have h1 : Nat.Coprime 2 (Nat.card E - 1) := Nat.coprime_two_left.mpr (odd_pred_of_even hE hE2)
    have := Nat.Coprime.pow_left 2 h1
    simpa using this
  have h : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [hg, Nat.div_one, h, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, show 4 * (4 - 1) / 2 = 6 by norm_num]
  ring

theorem not_dvd_u6_prod {Q : ℕ} (hQ : 2 ≤ Q) (hQ2 : 2 ∣ Q) :
    ¬ (Q ^ 4 + 1) ∣ Q ^ 15 * ((Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1) * (Q ^ 5 + 1) * (Q ^ 6 - 1)) := by
  intro h
  have hne : Q ^ 4 + 1 ≠ 1 := by
    have : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓX := dvd_trans hℓd h
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ Q ^ 4 := dvd_pow hQ2 (by norm_num)
    have := (Nat.dvd_add_right h2).1 hℓd
    omega
  have hQ1 : ∀ i, 1 ≤ Q ^ i := fun i => Nat.one_le_pow _ _ (by omega)
  have hd : ((Q : ZMod ℓ)) ^ 4 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).2 hℓd
    simpa using this
  have h2 : (2 : ZMod ℓ) = 0 → False := by
    intro h20
    have : ((2 : ℕ) : ZMod ℓ) = 0 := by simpa using h20
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).1 this
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hdvd)
  rcases (Nat.Prime.dvd_mul hℓ).1 hℓX with hA | hA
  ·
    have hℓQ : ℓ ∣ Q := hℓ.dvd_of_dvd_pow hA
    have : ℓ ∣ Q ^ 4 := dvd_pow hℓQ (by norm_num)
    have := (Nat.dvd_add_right this).1 hℓd
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 this)
  rcases (Nat.Prime.dvd_mul hℓ).1 hA with hA | hA6
  · rcases (Nat.Prime.dvd_mul hℓ).1 hA with hA | hA5
    · rcases (Nat.Prime.dvd_mul hℓ).1 hA with hA | hA4
      · rcases (Nat.Prime.dvd_mul hℓ).1 hA with hA2 | hA3
        ·
          have := (ZMod.natCast_eq_zero_iff _ _).2 hA2
          rw [Nat.cast_sub (hQ1 2)] at this
          push_cast at this
          apply h2
          linear_combination hd - ((Q : ZMod ℓ) ^ 2 + 1) * this
        ·
          have := (ZMod.natCast_eq_zero_iff _ _).2 hA3
          push_cast at this
          apply h2
          linear_combination (1 - ((Q : ZMod ℓ) ^ 2 + (Q : ZMod ℓ) + 1) * (Q : ZMod ℓ)) * this +
            ((Q : ZMod ℓ) ^ 2 + (Q : ZMod ℓ) + 1) * hd
      ·
        have := (ZMod.natCast_eq_zero_iff _ _).2 hA4
        rw [Nat.cast_sub (hQ1 4)] at this
        push_cast at this
        apply h2
        linear_combination hd - this
    ·
      have := (ZMod.natCast_eq_zero_iff _ _).2 hA5
      push_cast at this
      apply h2
      linear_combination (1 + ((Q : ZMod ℓ) ^ 4 + (Q : ZMod ℓ) ^ 3 + (Q : ZMod ℓ) ^ 2 + (Q : ZMod ℓ) + 1)) * this -
        ((Q : ZMod ℓ) ^ 4 + (Q : ZMod ℓ) ^ 3 + (Q : ZMod ℓ) ^ 2 + (Q : ZMod ℓ) + 1) * (Q : ZMod ℓ) * hd
  ·
    have := (ZMod.natCast_eq_zero_iff _ _).2 hA6
    rw [Nat.cast_sub (hQ1 6)] at this
    push_cast at this
    apply h2
    linear_combination (1 - ((Q : ZMod ℓ) ^ 2 - 1) * (Q : ZMod ℓ) ^ 2) * hd + ((Q : ZMod ℓ) ^ 2 - 1) * this


theorem not_dvd_card_psl_four {f e : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ f) ^ (2 * e)) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    ¬ Nat.card (StatedProj (StatedSL 4 E)) ∣ Nat.card (StatedProj (StatedSU 6 (2 ^ f) K)) := by
  intro hdvd
  have hQ2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQeven : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hR2 : 2 ≤ Nat.card E := by
    rw [hE]
    exact le_trans hQ2 (Nat.le_self_pow (by omega) _)
  have hRe : 2 ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow hQeven (by omega)
  rw [card_psl_four_eq hRe hR2] at hdvd
  rw [card_statedProj_statedSU Nat.prime_two hf hK (by norm_num),
    prod_icc_two_six (by omega), show 6 * (6 - 1) / 2 = 15 by norm_num] at hdvd
  generalize hQ : 2 ^ f = Q at *
  have hQ1 : ∀ i, 1 ≤ Q ^ i := fun i => Nat.one_le_pow _ _ (by omega)
  have hodd : Odd ((Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1) * (Q ^ 5 + 1) * (Q ^ 6 - 1)) := by
    have h2 : ∀ i, 1 ≤ i → 2 ∣ Q ^ i := fun i hi => dvd_pow hQeven (by omega)
    have h3 : ∀ i, 1 ≤ i → 2 ≤ Q ^ i := fun i hi => le_trans hQ2 (Nat.le_self_pow (by omega) _)
    exact ((((odd_pred_of_even (h3 2 (by norm_num)) (h2 2 (by norm_num))).mul
      (odd_succ_of_even (h2 3 (by norm_num)))).mul
      (odd_pred_of_even (h3 4 (by norm_num)) (h2 4 (by norm_num)))).mul
      (odd_succ_of_even (h2 5 (by norm_num)))).mul
      (odd_pred_of_even (h3 6 (by norm_num)) (h2 6 (by norm_num)))
  set P6 := (Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1) * (Q ^ 5 + 1) * (Q ^ 6 - 1) with hP6
  have hg : Nat.gcd 6 (Q + 1) ∣ Q ^ 15 * P6 := by
    have h1 : Nat.gcd 6 (Q + 1) ∣ Q + 1 := Nat.gcd_dvd_right _ _
    have h2 : Q + 1 ∣ Q ^ 3 + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow Q 1 (n := 3) (by decide)
      simpa using this
    have h3 : Q ^ 3 + 1 ∣ P6 := by
      rw [hP6]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_left (Q ^ 3 + 1) (Q ^ 2 - 1)) _) _) _
    exact (h1.trans (h2.trans h3)).mul_left _
  have hX : Nat.card E ^ 6 * ((Nat.card E ^ 2 - 1) * (Nat.card E ^ 3 - 1) * (Nat.card E ^ 4 - 1)) ∣
      Q ^ 15 * P6 :=
    hdvd.trans (Nat.div_dvd_of_dvd hg)
  have hA : ∀ R : ℕ, R ^ 4 - 1 ∣ R ^ 6 * ((R ^ 2 - 1) * (R ^ 3 - 1) * (R ^ 4 - 1)) := fun R =>
    (dvd_mul_left (R ^ 4 - 1) ((R ^ 2 - 1) * (R ^ 3 - 1))).trans (dvd_mul_left _ _)
  rcases Nat.lt_or_ge e 2 with he1 | he2
  · obtain rfl : e = 1 := by omega
    have hR : Nat.card E = Q ^ 2 := by rw [hE]
    rw [hR] at hX
    have hd1 : Q ^ 4 + 1 ∣ (Q ^ 2) ^ 4 - 1 := by
      obtain ⟨a, ha⟩ : ∃ a, Q ^ 4 = a + 1 := ⟨Q ^ 4 - 1, by have := hQ1 4; omega⟩
      rw [show (Q ^ 2) ^ 4 = (Q ^ 4) ^ 2 by ring, ha]
      exact ⟨a, by
        rw [show (a + 1) ^ 2 - 1 = a * (a + 2) by
          have : (a + 1) ^ 2 = a * (a + 2) + 1 := by ring
          omega]
        ring⟩
    exact not_dvd_u6_prod hQ2 hQeven (hd1.trans ((hA _).trans hX))
  · have hpow : 2 ^ (f * (12 * e)) ∣ 2 ^ (f * 15) * P6 := by
      have h1 : Nat.card E ^ 6 ∣ Q ^ 15 * P6 :=
        (Dvd.intro _ rfl : Nat.card E ^ 6 ∣ Nat.card E ^ 6 * _).trans hX
      rw [hE, ← hQ] at h1
      rw [← pow_mul, ← pow_mul, ← pow_mul] at h1
      have e1 : f * (2 * e * 6) = f * (12 * e) := by ring
      rw [e1] at h1
      exact h1
    have hcop : Nat.Coprime (2 ^ (f * (12 * e))) P6 :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have h2 := hcop.dvd_of_dvd_mul_right hpow
    have h3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 h2
    have h4 : 12 * e ≤ 15 := Nat.le_of_mul_le_mul_left h3 (by omega)
    omega


theorem ordD_five_lt_ordTwistedD_five {f : ℕ} (hf : 1 ≤ f) : ordD 5 (2 ^ f) < ordTwistedD 5 (2 ^ f) := by
  have hQ2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQeven : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  generalize 2 ^ f = q at *
  have hq5 : 2 ≤ q ^ 5 := le_trans hQ2 (Nat.le_self_pow (by norm_num) _)
  have hq5e : 2 ∣ q ^ 5 := dvd_pow hQeven (by norm_num)
  have g1 : Nat.gcd 4 (q ^ 5 - 1) = 1 := by
    obtain ⟨k, hk⟩ := hq5e
    have h1 : Nat.Coprime 2 (q ^ 5 - 1) := Nat.coprime_two_left.mpr ⟨k - 1, by omega⟩
    simpa using Nat.Coprime.pow_left 2 h1
  have g2 : Nat.gcd 4 (q ^ 5 + 1) = 1 := by
    obtain ⟨k, hk⟩ := hq5e
    have h1 : Nat.Coprime 2 (q ^ 5 + 1) := Nat.coprime_two_left.mpr ⟨k, by omega⟩
    simpa using Nat.Coprime.pow_left 2 h1
  unfold ordD ordTwistedD
  rw [g1, g2, Nat.div_one, Nat.div_one]
  have hP : 0 < ∏ i ∈ Finset.Icc 1 (5 - 1), (q ^ (2 * i) - 1) := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have : 2 ≤ q ^ (2 * i) := le_trans hQ2 (Nat.le_self_pow (by omega) _)
    omega
  have hq0 : 0 < q ^ (5 * (5 - 1)) := (Nat.pow_pos (by omega))
  apply Nat.mul_lt_mul_of_pos_right _ hP
  apply Nat.mul_lt_mul_of_pos_left _ hq0
  omega


theorem no_psl_four_in_psu_six {f e : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ f) ^ (2 * e))
    (J : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K)))
    (φ : ↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL 4 E)) : False := by
  apply not_dvd_card_psl_four hf he hE hK
  rw [← Nat.card_congr φ.toEquiv]
  have h1 : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card ↥J := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
    exact ⟨_, by rw [this, mul_comm]⟩
  exact h1.trans (Subgroup.card_subgroup_dvd_card J)

theorem no_omega_minus_five_in_omega_plus {G : Type} [Group G] [Finite G] {f : ℕ} (hf : 1 ≤ f)
    (hG : Nat.card G = ordD 5 (2 ^ f)) (J : Subgroup G)
    (hJ : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .POmegaMinus 5 2 f) : False := by
  have hcJ : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedD 5 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hJ).2.2.2.2 rfl
  have h1 : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card G := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
    have h2 : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card ↥J := ⟨_, by rw [this, mul_comm]⟩
    exact h2.trans (Subgroup.card_subgroup_dvd_card J)
  have hle := Nat.le_of_dvd Nat.card_pos h1
  rw [hcJ, hG] at hle
  exact absurd hle (not_le.2 (ordD_five_lt_ordTwistedD_five hf))

end CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC
