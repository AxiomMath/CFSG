module

public import CFSG.Dihedral.GorensteinWalter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.PerfectGroups
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

private lemma prime_dvd_315 {p : ℕ} (hp : Nat.Prime p) (h : p ∣ 315) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have h315 : (315 : ℕ) = 3 * (3 * (5 * 7)) := by norm_num
  rw [h315] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h))

theorem simple_card_eq_sixty
    {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] (hnonab : ∃ a b : Y, a * b ≠ b * a)
    (hdvd : Nat.card Y ∣ 20160) {m : ℕ} (hm : Odd m) (hcard : Nat.card Y = 4 * m) :
    Nat.card Y = 60 := by
  have hcomm : commutator Y = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      have hcen : Subgroup.center Y = ⊤ := (commutator_eq_bot_iff_center_eq_top Y).mp h
      exact hab ((Subgroup.mem_center_iff.mp (hcen ▸ Subgroup.mem_top a) b).symm)
    · exact h
  haveI : Group.IsPerfect Y := ⟨hcomm⟩
  obtain ⟨P, hPdih⟩ := exists_sylow_dihedral_two_of_card_four_mul_odd hm hcard
  have hP : ∃ n, Nonempty ((P : Subgroup Y) ≃* DihedralGroup n) := ⟨2, hPdih⟩
  rcases CFSG.GorensteinWalter.gorenstein_walter Y hnonab P hP with hA7 | hPSL
  ·
    obtain ⟨e⟩ := hA7
    have hY2520 : Nat.card Y = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hY2520] at hcard
    obtain ⟨t, ht⟩ := hm
    omega
  ·
    obtain ⟨p, k, hp, hpodd, h5, he⟩ := hPSL
    obtain ⟨e⟩ := he
    haveI : Fact p.Prime := hp
    have hk_ne : k ≠ 0 := by rintro rfl; norm_num at h5
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk_ne
    have hFcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk_ne
    have hIp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hp.out, hpodd, hk1, hFcard⟩
    have hYcard : Nat.card Y = p ^ k * ((p ^ k) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.GorensteinWalter.psl2_card_formula (GaloisField p k) hIp, hFcard]
    have hoddq : Odd (p ^ k) := hpodd.pow
    have h2dvd : 2 ∣ (p ^ k) ^ 2 - 1 :=
      even_iff_two_dvd.mp (Nat.Odd.sub_odd hoddq.pow odd_one)
    have hYq : Nat.card Y = p ^ k * (((p ^ k) ^ 2 - 1) / 2) := by
      rw [hYcard, Nat.mul_div_assoc (p ^ k) h2dvd]
    have hq_dvd_Y : p ^ k ∣ Nat.card Y := by
      rw [hYq]; exact dvd_mul_right _ _
    have hq_dvd_20160 : p ^ k ∣ 20160 := dvd_trans hq_dvd_Y hdvd
    have hp_cases : p = 3 ∨ p = 5 ∨ p = 7 := by
      have h20160 : (20160 : ℕ) = 315 * 64 := by norm_num
      rw [h20160] at hq_dvd_20160
      have hp_dvd : p ∣ 315 * 64 := dvd_trans (dvd_pow_self p hk_ne) hq_dvd_20160
      rcases (Nat.Prime.dvd_mul hp.out).mp hp_dvd with h | h
      · exact prime_dvd_315 hp.out h
      · exfalso
        have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
        rw [h64] at h
        have hp2 : p = 2 :=
          (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h)
        subst hp2
        norm_num at hpodd
    have hk_le : k ≤ 9 := by
      have hp3 : 3 ≤ p := by rcases hp_cases with rfl | rfl | rfl <;> norm_num
      have hqle : p ^ k ≤ 20160 := Nat.le_of_dvd (by norm_num) hq_dvd_20160
      have h3le : 3 ^ k ≤ 20160 := le_trans (Nat.pow_le_pow_left hp3 k) hqle
      by_contra h
      have h10 : 10 ≤ k := by omega
      have hbig : 3 ^ 10 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h10
      have : (59049 : ℕ) ≤ 3 ^ k := by simpa using hbig
      omega
    have hq_cases : p ^ k = 5 ∨ p ^ k = 7 ∨ p ^ k = 9 := by
      rcases hp_cases with rfl | rfl | rfl
      · refine (show (5 ≤ 3 ^ k ∧ 3 ^ k ∣ 20160) → (3 ^ k = 5 ∨ 3 ^ k = 7 ∨ 3 ^ k = 9)
          from by interval_cases k <;> decide) ⟨h5, hq_dvd_20160⟩
      · refine (show (5 ≤ 5 ^ k ∧ 5 ^ k ∣ 20160) → (5 ^ k = 5 ∨ 5 ^ k = 7 ∨ 5 ^ k = 9)
          from by interval_cases k <;> decide) ⟨h5, hq_dvd_20160⟩
      · refine (show (5 ≤ 7 ^ k ∧ 7 ^ k ∣ 20160) → (7 ^ k = 5 ∨ 7 ^ k = 7 ∨ 7 ^ k = 9)
          from by interval_cases k <;> decide) ⟨h5, hq_dvd_20160⟩
    rcases hq_cases with hq | hq | hq
    · rw [hYq, hq]; norm_num
    · exfalso
      have h168 : Nat.card Y = 168 := by rw [hYq, hq]; norm_num
      rw [h168] at hcard
      obtain ⟨t, ht⟩ := hm
      omega
    · exfalso
      have h360 : Nat.card Y = 360 := by rw [hYq, hq]; norm_num
      rw [h360] at hcard
      obtain ⟨t, ht⟩ := hm
      omega

end CFSG.EvenSporadicStandard.HNRecog.GH73
