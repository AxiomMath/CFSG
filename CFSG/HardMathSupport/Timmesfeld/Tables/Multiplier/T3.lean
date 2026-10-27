module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Linear
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Main

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Multiplier TauCeti
open CFSG.Open (GriessAllModelsStatement)
open CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem nine_dvd_of_nine_dvd_lcm {a : ℕ} (ha : 0 < a) (h : 9 ∣ Nat.lcm a 12) : 9 ∣ a := by
  by_contra hna
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hle : a.factorization 3 ≤ 1 := by
    by_contra hlt
    push Not at hlt
    exact hna (by
      have := (h3.pow_dvd_iff_le_factorization ha.ne').2 (show 2 ≤ a.factorization 3 by omega)
      simpa using this)
  have hl : (Nat.lcm a 12).factorization 3 ≤ 1 := by
    rw [Nat.factorization_lcm ha.ne' (by norm_num)]
    have h12 : (12 : ℕ).factorization 3 = 1 := by
      have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization h3]
      simp
    simp [h12, hle]
  have := (h3.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha.ne' (by norm_num))).1
    (by simpa using h : 3 ^ 2 ∣ Nat.lcm a 12)
  omega

theorem not_dvd_of_small {r x : ℕ} (hr : 5 ≤ r) (h0 : 0 < x) (h4 : x ≤ 4) : ¬ r ∣ x :=
  fun hd => by have := Nat.le_of_dvd h0 hd; omega

theorem tables112_T3 (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hK : CFSG.Open.IsKGroup L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : IsPGroup p (Subgroup.center L)) (h1 : CFSG.Open.pRank p (Subgroup.center L) = 1) :
    (p = 3 ∧ Nat.card (Subgroup.center L) = 3) ∨
      p + 2 ≤ (p - 2) * CFSG.Open.pRank p (⊤ : Subgroup L) := by
  have : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect L := ⟨hq.1⟩
  have hq' : CFSG.IsQuasisimple L :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      L hq⟩
  have hpZ : p ∣ Nat.card (Subgroup.center L) := by
    obtain ⟨E, hEZ, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center L)
    rw [h1, pow_one] at hEcard
    exact hEcard ▸ Subgroup.card_dvd_of_le hEZ
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [hk] at hpZ
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpZ)
  have hm2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) := by
    have hpL : p ∣ Nat.card L := hpZ.trans (Subgroup.card_subgroup_dvd_card _)
    have h := (CFSG.SectionRank.perfect_cyclic_center_odd_elements hp2 hpL).2 hpZ
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  rcases centralQuotient_family hq hK with hF | ⟨d, ⟨e⟩⟩ | ⟨s, ⟨e⟩⟩
  · exact Tables.Alt.tables112On_alt.T3 L hF hq hK p hp hp2 hZ h1
  · by_cases hmain : p = 3 ∧ Nat.card (Subgroup.center L) = 3
    · exact Or.inl hmain
    refine Or.inr ?_
    by_cases hp7 : 7 ≤ p
    · calc p + 2 ≤ (p - 2) * 2 := by omega
        _ ≤ _ := Nat.mul_le_mul_left _ hm2
    have hp35 : p = 5 ∨ p = 3 := by
      have h3 : 3 ≤ p := hp.two_le.lt_of_ne (Ne.symm hp2)
      interval_cases p
      · exact Or.inr rfl
      · exact absurd hp (by norm_num)
      · exact Or.inl rfl
      · exact absurd hp (by norm_num)
    obtain ⟨t, n, p', f', hm⟩ := exists_lieModel d
    have hdvdT := center_dvd_table hGA hq' e hm
    have hb := genericOrders_snd_le t n p' f'
    have hcd := exceptionalOrders_le t n p' f'
    have ha0 := genericOrders_fst_pos hm.1
    have hQ : ∃ Q : ℕ, 5 ≤ Q ∧ (p = 5 → Q = 5) ∧ (p = 3 → Q = 9) ∧ p ∣ Q ∧
        Q ∣ (genericOrders t n p' f').1 := by
      rcases hp35 with rfl | rfl
      · refine ⟨5, le_rfl, fun _ => rfl, fun h => absurd h (by norm_num), dvd_rfl, ?_⟩
        have h5 : 5 ∣ (genericOrders t n p' f').1 * (genericOrders t n p' f').2 *
            ((exceptionalOrders t n p' f').1 * (exceptionalOrders t n p' f').2) := by
          have : 5 ∣ Nat.card (Subgroup.center L) := hpZ
          exact this.trans hdvdT
        have hp5 : Nat.Prime 5 := hp
        rcases (hp5.dvd_mul).1 h5 with h | h
        · rcases (hp5.dvd_mul).1 h with h | h
          · exact h
          · exact absurd h (not_dvd_of_small (by norm_num) hb.1 (by omega))
        · rcases (hp5.dvd_mul).1 h with h | h
          · exact absurd h (not_dvd_of_small (by norm_num) hcd.1.1 hcd.1.2)
          · exact absurd h (not_dvd_of_small (by norm_num) hcd.2.1 hcd.2.2)
      · refine ⟨9, by norm_num, fun h => absurd h (by norm_num), fun _ => rfl, by norm_num, ?_⟩
        have hk2 : 2 ≤ k := by
          by_contra hlt
          have : k = 1 := by omega
          rw [this, pow_one] at hk
          exact hmain ⟨rfl, hk⟩
        by_contra h9
        have hz3 : ∀ z : Subgroup.center L, z ^ 3 = 1 := by
          intro z
          have hz := center_pow_lcm hGA hq e hm z
          obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hZ z
          have hdv : 3 ^ j ∣ Nat.lcm (genericOrders t n p' f').1 12 :=
            hj ▸ orderOf_dvd_of_pow_eq_one hz
          by_cases hj2 : 2 ≤ j
          · exfalso
            exact h9 (nine_dvd_of_nine_dvd_lcm ha0 (by
              have : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 hj2
              simpa using this.trans hdv))
          · have : j ≤ 1 := by omega
            interval_cases j
            · rw [pow_zero, orderOf_eq_one_iff] at hj
              rw [hj, one_pow]
            · rw [pow_one] at hj
              rw [← hj]
              exact pow_orderOf_eq_one z
        have hEab : CFSG.Open.IsElemAbelian 3 (Subgroup.center L) :=
          ⟨inferInstance, fun x hx => congrArg Subtype.val (hz3 ⟨x, hx⟩)⟩
        have hle := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hEab hk
        omega
    obtain ⟨Q, hQ5, hQ5', hQ3, hpQ, hQa⟩ := hQ
    have ht : t = .PSL ∨ t = .PSU := by
      by_contra hnt
      push Not at hnt
      have := genericOrders_fst_le_four hnt.1 hnt.2 n p' f'
      have := Nat.le_of_dvd ha0 hQa
      omega
    have hnQ : Q ∣ n := by
      rcases ht with rfl | rfl
      · exact hQa.trans (Nat.gcd_dvd_left _ _)
      · exact hQa.trans (Nat.gcd_dvd_left _ _)
    have hn0 : n ≠ 0 := by
      rcases ht with rfl | rfl
      · have := hm.1.2.2.1; omega
      · have := hm.1.2.2.1; omega
    have hn4 : Q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hnQ
    have hpa : p ∣ (genericOrders t n p' f').1 := hpQ.trans hQa
    have hbcd : ¬ p ∣ (genericOrders t n p' f').2 ∧ ¬ p ∣ (exceptionalOrders t n p' f').1 ∧
        ¬ p ∣ (exceptionalOrders t n p' f').2 := by
      rcases hp35 with rfl | rfl
      · exact ⟨not_dvd_of_small (by norm_num) hb.1 (by omega),
          not_dvd_of_small (by norm_num) hcd.1.1 hcd.1.2,
          not_dvd_of_small (by norm_num) hcd.2.1 hcd.2.2⟩
      · obtain ⟨hc3, hd3⟩ := not_three_dvd_exceptional_of_dvd_generic hpa
        exact ⟨fun hd => by have := Nat.le_of_dvd hb.1 hd; omega, hc3, hd3⟩
    have hrank := rank_ge_of_model hGA hperf hp hp2 hZ e hm ht (by omega) hpa hbcd.1 hbcd.2.1
      hbcd.2.2
    rcases hp35 with rfl | rfl
    · have := hQ5' rfl
      subst this
      have : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup L) := by omega
      omega
    · have := hQ3 rfl
      subst this
      have : 7 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by omega
      omega
  ·
    refine Or.inl ?_
    have hd := card_center_dvd_twelve hSpM hq s e
    have hp12 : p ∣ 12 := hpZ.trans hd
    have hp3 : p = 3 := by
      have h12 : p ∣ 2 ^ 2 * 3 := by norm_num; exact hp12
      rcases (hp.dvd_mul).1 h12 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
    subst hp3
    refine ⟨rfl, ?_⟩
    have hk1 : k = 1 := by
      by_contra hne
      have hk2 : 2 ≤ k := by omega
      have h9 : 3 ^ 2 ∣ 12 := (pow_dvd_pow 3 hk2).trans (hk ▸ hd)
      norm_num at h9
    rw [hk, hk1, pow_one]

theorem tables112_T3_field (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers) :
    ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
      ∀ p : ℕ, p.Prime → p ≠ 2 → IsPGroup p (Subgroup.center L) →
        CFSG.Open.pRank p (Subgroup.center L) = 1 →
        (p = 3 ∧ Nat.card (Subgroup.center L) = 3) ∨
          p + 2 ≤ (p - 2) * CFSG.Open.pRank p (⊤ : Subgroup L) :=
  fun _ _ _ hq hK _ hp hp2 hZ h1 => tables112_T3 hGA hSpM hq hK hp hp2 hZ h1

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
