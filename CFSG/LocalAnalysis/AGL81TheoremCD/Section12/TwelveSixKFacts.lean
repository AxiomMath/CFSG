module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Small
import CFSG.CGT.PushingUpLit.CGT6.SixFourLTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem prime_dvd_card_mulAut_of_lieModel_psp43 {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSp 2 3 1) {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card (MulAut X)) : r = 2 ∨ r = 3 ∨ r = 5 := by
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.psp43_equiv_of_lieModel hX
  have hcard : Nat.card (MulAut X) =
      Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hdvd' : r ∣ Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) := by
    rwa [← hcard]
  have hdvd25920 : 25920 ∣ Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.dvd_25920_mulAut_PSp43
  have hle : Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) ≤ 51840 :=
    CFSG.Quasithin.SimsF5.card_mulAut_PSp43_le
  have hpos : 0 < Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) := by
    haveI : Nonempty (MulAut CFSG.GH74.Exceptional.PSp43) := ⟨1⟩
    exact Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd25920
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, mul_zero] at hk
      omega
    · exact hkpos
  have hk2 : k ≤ 2 := by
    have h : 25920 * k ≤ 25920 * 2 := by
      calc 25920 * k = Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) := hk.symm
        _ ≤ 51840 := hle
        _ = 25920 * 2 := by norm_num
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hdvd51840 : r ∣ 51840 := by
    rw [hk] at hdvd'
    rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
    · exact hdvd'.trans (by norm_num)
    · simpa using hdvd'
  have hmem : r ∈ (51840 : ℕ).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hr, hdvd51840, by norm_num⟩
  rw [show (51840 : ℕ).primeFactors = {2, 3, 5} by norm_num [Nat.primeFactors]] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem

theorem prime_dvd_card_centralizer_perm_nine {σ : Equiv.Perm (Fin 9)} (hσ : orderOf σ = 3)
    {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 9))))) :
    r = 2 ∨ r = 3 ∨ r = 5 := by
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [hσ]; exact Nat.prime_three)
  rw [hσ] at hk
  have hk1 : k + 1 ≠ 0 := by omega
  have hsum := Equiv.Perm.sum_cycleType_le σ
  rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hk3 : k ≤ 2 := by omega
  have hcard : Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 9)))) =
      (9 - (k + 1) * 3).factorial * 3 ^ (k + 1) * (k + 1).factorial := by
    rw [Equiv.Perm.nat_card_centralizer, hk, Multiset.sum_replicate, Multiset.prod_replicate,
      Multiset.toFinset_replicate, ite_eq_right hk1, Finset.prod_singleton,
      Multiset.count_replicate_self, Fintype.card_fin, smul_eq_mul]
  have hdvd38880 : r ∣ 38880 := by
    have h := hdvd
    rw [hcard] at h
    interval_cases k <;> norm_num at h
    · exact h.trans (by norm_num)
    · exact h.trans (by norm_num)
    · exact h.trans (by norm_num)
  have hmem : r ∈ (38880 : ℕ).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hr, hdvd38880, by norm_num⟩
  rw [show (38880 : ℕ).primeFactors = {2, 3, 5} by norm_num [Nat.primeFactors]] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem

theorem exists_prime_seven_le_dvd_two_pow_sub_one {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ 7 ≤ r ∧ r ∣ 2 ^ n - 1 := by
  have hge : 7 ≤ 2 ^ n - 1 := by
    have h : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    norm_num at h
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ n - 1 ≠ 1)
  have hodd : Odd (2 ^ n - 1) := by
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    obtain ⟨c, hc⟩ := h2
    have hpos : 0 < 2 ^ n := by positivity
    exact ⟨c - 1, by omega⟩
  have hne2 : r ≠ 2 := by
    intro h
    subst h
    exact hodd.not_two_dvd_nat hrdvd
  have hne3 : r ≠ 3 := by
    intro h
    subst h
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_not_three_dvd_sub_one hn
      hrdvd
  have hne5 : r ≠ 5 := by
    intro h
    subst h
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_not_five_dvd_sub_one hn
      hrdvd
  have hr7 : 7 ≤ r := by
    have hr2 : 2 ≤ r := hr.two_le
    by_contra hlt
    have hr6 : r ≤ 6 := by omega
    interval_cases r
    · exact absurd rfl hne2
    · exact absurd rfl hne3
    · exact absurd hr (by norm_num)
    · exact absurd rfl hne5
    · exact absurd hr (by norm_num)
  exact ⟨r, hr, hr7, hrdvd⟩

theorem eq_one_of_isPSLType_two_of_primes {n : ℕ} (hn : Odd n) {X : Type} [Group X] [Finite X]
    (hX : IsPSLType 2 (GaloisField 2 n) X)
    (h235 : ∀ r : ℕ, r.Prime → r ∣ Nat.card X → r = 2 ∨ r = 3 ∨ r = 5) : n = 1 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  unfold CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPSLType at hX
  obtain ⟨e⟩ := hX
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have hcardPSL : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        (GaloisField 2 n)).toEquiv]
    exact CFSG.CGT.PushingUpLit.CGT6.card_psl2_two_pow hn1 hF
  have hcardX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    (Nat.card_congr e.toEquiv).trans hcardPSL
  have hdvd : 2 ^ n - 1 ∣ Nat.card X := by
    rw [hcardX]
    exact dvd_mul_of_dvd_right (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2) _
  by_contra hne1
  have hge3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  obtain ⟨r, hr, hr7, hrdvd⟩ := exists_prime_seven_le_dvd_two_pow_sub_one hn hge3
  exact absurd (h235 r hr (hrdvd.trans hdvd)) (by omega)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
