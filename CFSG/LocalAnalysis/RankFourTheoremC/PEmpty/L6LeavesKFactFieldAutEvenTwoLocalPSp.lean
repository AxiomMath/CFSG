module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenTwoLocalPSL

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj StatedSp)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor LieOrderFormulasInput)

theorem twoLocalWhen_PSp (hLie : LieOrderFormulasInput) :
    TwoLocalWhen .PSp (fun n f₀ => ¬ IsExcRow .PSp n f₀) := by
  intro K _ _ hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf
  have hcl0 : StatedClassicalModel K .PSp n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hf1 : 1 ≤ f := hadm.2.1
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  have hp2 : p ≠ 2 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hform, -⟩ := hLie K .PSp n 2 f hadm hmodel
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
    have hmem : (p - 1) / 2 ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hdouble : 2 * ((p - 1) / 2) = p - 1 := by omega
    have hprod : p ∣ ∏ i ∈ Finset.Icc 1 n, ((2 ^ f) ^ (2 * i) - 1) := by
      have h1 : (2 ^ f) ^ (2 * ((p - 1) / 2)) - 1 = (2 ^ f) ^ (p - 1) - 1 := by rw [hdouble]
      exact (h1 ▸ hferm).trans (Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) hmem)
    have hnum : p ∣ lieOrderNumerator .PSp n (2 ^ f) := Dvd.dvd.mul_left hprod _
    rw [← hform] at hnum
    rcases (Nat.Prime.dvd_mul hp).1 hnum with h | h
    · exact hpK h
    · exact hdiv h
  obtain ⟨r, m, hrm, hm, hcorr⟩ := exists_ppd_data hf₀ (by omega : 2 ≤ 2 * n)
    (fun h => hP ⟨h.1, Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))⟩)
  have hppd := fun k => ppd_dvd_iff hrm hm hcorr hp hpn k
  have hr : r.Prime := hrm.1
  obtain ⟨-, F, hF, hFfin, hFcard, ⟨e⟩⟩ := hcl0
  haveI : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard'
  have hfin : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  refine ⟨r, hr, fun R hR2 hR1 => ?_⟩
  have hRn : ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set K)) := by
    refine not_dvd_card_normalizer_of_equiv e hr (by rw [hfin]; omega)
      (by rw [hfin, hFcard, hf]; exact (hppd (2 * n)).2.2 (dvd_refl _)) (fun k hk hk' => ?_) R hR2
      hR1
    rw [hfin] at hk'
    rw [hFcard, hf]
    intro h
    exact absurd (Nat.le_of_dvd hk ((hppd k).2.1 h)) (not_le.mpr hk')
  have hq1 : ¬ r ∣ 2 ^ f₀ - 1 := by
    intro h
    have h1 := (hppd 1).1
    rw [pow_one] at h1
    have h2 := h1.1 h
    exact absurd (Nat.le_of_dvd one_pos h2) (by omega)
  have hdr : ¬ r ∣ lieOrderDivisor .PSp n (2 ^ f₀) :=
    fun h => hq1 (h.trans (Nat.gcd_dvd_right 2 (2 ^ f₀ - 1)))
  have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
  have hrn : r ∣ lieOrderNumerator .PSp n (2 ^ f₀) := by
    have hmem : n ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
    have h1 : r ∣ (2 ^ f₀) ^ (2 * n) - 1 := ((hppd (2 * n)).1).2 (dvd_refl _)
    exact Dvd.dvd.mul_left (h1.trans
      (Finset.dvd_prod_of_mem (fun i => (2 ^ f₀) ^ (2 * i) - 1) hmem)) _
  have hnum0 : lieOrderNumerator .PSp n (2 ^ f₀) ≠ 0 := by
    simp only [lieOrderNumerator]
    refine mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)) ?_
    refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have := Nat.one_lt_pow (by omega : 2 * i ≠ 0) hq2
    omega
  exact padicValNat_add_lt_of_not_dvd hr hRn hdr hnum0 hrn

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
