module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenTwoLocalPSL

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj StatedSU)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor LieOrderFormulasInput)

theorem twoLocalWhen_PSU_odd (hLie : LieOrderFormulasInput) :
    TwoLocalWhen .PSU (fun n f₀ => Odd n ∧ ¬ IsExcRow .PSU n f₀) := by
  intro K _ _ hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf
  obtain ⟨hnodd, hexc⟩ := hP
  have hcl0 : StatedClassicalModel K .PSU n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hf1 : 1 ≤ f := hadm.2.1
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  have hp2 : p ≠ 2 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hform, -⟩ := hLie K .PSU n 2 f hadm hmodel
  have hpn : ¬ p ∣ 2 * n := by
    intro h
    have hp2' : ¬ p ∣ 2 := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    have hpn : p ∣ n := ((Nat.Prime.dvd_mul hp).1 h).resolve_left hp2'
    have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
    have hp2f : ¬ p ∣ 2 ^ f := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow h))
    have hferm := prime_dvd_pow_sub_one hp hp2f
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h2 | h2
      · exact absurd h2 hp2
      · exact h2
    have hmem : p - 1 ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hev : Even (p - 1) := by
      rw [Nat.even_iff]
      omega
    have hprod : p ∣ ∏ i ∈ Finset.Icc 2 n,
        (if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1) := by
      have := Finset.dvd_prod_of_mem
        (fun i => if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1) hmem
      simp only [hev, if_true] at this
      exact hferm.trans this
    have hnum : p ∣ lieOrderNumerator .PSU n (2 ^ f) := Dvd.dvd.mul_left hprod _
    rw [← hform] at hnum
    rcases (Nat.Prime.dvd_mul hp).1 hnum with h | h
    · exact hpK h
    · exact hdiv h
  obtain ⟨r, m, hrm, hm, hcorr⟩ := exists_ppd_data hf₀ (by omega : 2 ≤ 2 * n)
    (fun h => hexc ⟨h.1, Or.inr (Or.inl ⟨rfl, Or.inl (by omega)⟩)⟩)
  have hppd := fun k => ppd_dvd_iff hrm hm hcorr hp hpn k
  have hr : r.Prime := hrm.1
  obtain ⟨-, F, hF, hFfin, hFcard, ⟨e⟩⟩ := hcl0
  haveI : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 2 ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card, hFcard, ← pow_mul, mul_comm]
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard'
  have hFq : Nat.card F = (2 ^ (p * f₀)) ^ 2 := by rw [hFcard, hf]
  have hFpow : ∀ k : ℕ, Nat.card F ^ k = (2 ^ (p * f₀)) ^ (2 * k) := fun k => by
    rw [hFq, ← pow_mul]
  refine ⟨r, hr, fun R hR2 hR1 => ?_⟩
  have hRn : ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set K)) := by
    refine not_dvd_card_normalizer_of_equiv e hr (by rw [Fintype.card_fin]; omega)
      (by rw [Fintype.card_fin, hFpow]; exact (hppd (2 * n)).2.2 (dvd_refl _))
      (fun k hk hk' => ?_) R hR2 hR1
    rw [Fintype.card_fin] at hk'
    rw [hFpow]
    intro h
    have h2 := (hppd (2 * k)).2.1 h
    have h3 : n ∣ k := (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).1 h2
    exact absurd (Nat.le_of_dvd hk h3) (not_le.mpr hk')
  have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
  have hAn : 1 ≤ (2 ^ f₀) ^ n := Nat.one_le_pow _ _ (by omega)
  have hrA : r ∣ (2 ^ f₀) ^ n + 1 := by
    have h1 : r ∣ (2 ^ f₀) ^ (2 * n) - 1 := ((hppd (2 * n)).1).2 (dvd_refl _)
    have h2 : (2 ^ f₀) ^ (2 * n) - 1 = ((2 ^ f₀) ^ n - 1) * ((2 ^ f₀) ^ n + 1) := by
      rw [sub_one_mul_add_one hAn, ← sq]
      congr 1
      ring
    rw [h2] at h1
    rcases (Nat.Prime.dvd_mul hr).1 h1 with h | h
    · exact absurd (((hppd n).1).1 h) (fun h' => absurd (Nat.le_of_dvd (by omega) h')
        (by omega))
    · exact h
  have hq1 : ¬ r ∣ 2 ^ f₀ + 1 := by
    intro h
    have hA1 : 1 ≤ 2 ^ f₀ := by omega
    have h1 : r ∣ (2 ^ f₀ - 1) * (2 ^ f₀ + 1) := Dvd.dvd.mul_left h _
    rw [sub_one_mul_add_one hA1] at h1
    have h2 : r ∣ (2 ^ f₀) ^ 2 - 1 := by rwa [sq]
    have h3 := ((hppd 2).1).1 h2
    exact absurd (Nat.le_of_dvd (by omega) h3) (by omega)
  have hdr : ¬ r ∣ lieOrderDivisor .PSU n (2 ^ f₀) :=
    fun h => hq1 (h.trans (Nat.gcd_dvd_right n (2 ^ f₀ + 1)))
  have hnodd' : ¬ Even n := Nat.not_even_iff_odd.2 hnodd
  have hrn : r ∣ lieOrderNumerator .PSU n (2 ^ f₀) := by
    have hmem : n ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
    have := Finset.dvd_prod_of_mem
      (fun i => if Even i then (2 ^ f₀) ^ i - 1 else (2 ^ f₀) ^ i + 1) hmem
    simp only [hnodd', if_false] at this
    exact Dvd.dvd.mul_left (hrA.trans this) _
  have hnum0 : lieOrderNumerator .PSU n (2 ^ f₀) ≠ 0 := by
    simp only [lieOrderNumerator]
    refine mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)) ?_
    refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have := Nat.one_lt_pow (by omega : i ≠ 0) hq2
    split_ifs
    · omega
    · omega
  exact padicValNat_add_lt_of_not_dvd hr hRn hdr hnum0 hrn

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
