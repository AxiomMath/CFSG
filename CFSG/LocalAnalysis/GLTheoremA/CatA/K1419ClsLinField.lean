module


public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419Facts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open Polynomial

theorem k1419ClsLinField_dvd_finrank {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hω : ∃ w : K, w ^ 3 = 1 ∧ w ≠ 1) {a : L}
    (ha : a ∉ (algebraMap K L).range) (ha3 : a ^ 3 ∈ (algebraMap K L).range) :
    3 ∣ Module.finrank K L := by
  obtain ⟨ω, hω3, hωne⟩ := hω
  obtain ⟨c, hc⟩ := ha3
  have ha_ne : a ≠ 0 := by
    intro h
    subst h
    exact ha ⟨0, map_zero _⟩
  have hc_ne : c ≠ 0 := by
    intro h
    subst h
    rw [map_zero] at hc
    exact pow_ne_zero 3 ha_ne hc.symm
  have hpa : IsIntegral K a := IsIntegral.of_finite K a
  set p : Polynomial K := minpoly K a with hp_def
  have hp_monic : p.Monic := by
    rw [hp_def]
    exact minpoly.monic hpa
  have hdeg3 : (X ^ 3 - C c : Polynomial K).natDegree = 3 := Polynomial.natDegree_X_pow_sub_C
  have hf_ne : (X ^ 3 - C c : Polynomial K) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg3
    exact absurd hdeg3 (by norm_num)
  have hdvd : p ∣ X ^ 3 - C c := by
    rw [hp_def]
    apply minpoly.dvd
    have h : Polynomial.aeval a (X ^ 3 - C c : Polynomial K) = a ^ 3 - algebraMap K L c := by
      rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C]
    rw [h, hc, sub_self]
  have hle : p.natDegree ≤ 3 := by
    have := Polynomial.natDegree_le_of_dvd hdvd hf_ne
    rwa [hdeg3] at this
  have hge : 2 ≤ p.natDegree := by
    rw [hp_def]
    exact (minpoly.two_le_natDegree_iff hpa).mpr ha
  have hsumK : 1 + ω + ω ^ 2 = 0 := by
    have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      have h : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
      rw [h, hω3]; ring
    have h : ω ^ 2 + ω + 1 = 0 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (sub_eq_zero.mp h) hωne
      · exact h
    rw [show (1 : K) + ω + ω ^ 2 = ω ^ 2 + ω + 1 by ring]
    exact h
  have hne2 : p.natDegree ≠ 2 := by
    intro h2
    obtain ⟨q, hq⟩ := hdvd
    have hf_monic : (X ^ 3 - C c : Polynomial K).Monic :=
      Polynomial.monic_X_pow_sub_C c (by norm_num)
    have hq_ne : q ≠ 0 := by
      intro h
      rw [h, mul_zero] at hq
      exact hf_ne hq
    have hq_monic : q.Monic := hp_monic.of_mul_monic_left (hq ▸ hf_monic)
    have hq_deg : q.natDegree = 1 := by
      have h3 : (p * q).natDegree = 3 := by rw [← hq]; exact hdeg3
      rw [hp_monic.natDegree_mul hq_monic] at h3
      omega
    set r : K := -(q.coeff 0) with hr_def
    have hq_eq : q = X - C r := by
      rw [hq_monic.eq_X_add_C hq_deg, hr_def]
      simp
    have hfeval : Polynomial.eval r (X ^ 3 - C c : Polynomial K) = 0 := by
      rw [hq, Polynomial.eval_mul, hq_eq]
      simp
    have hcr : r ^ 3 = c := by
      have h := hfeval
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] at h
      exact sub_eq_zero.mp h
    set ωL : L := algebraMap K L ω with hωL
    have hsumL : 1 + ωL + ωL ^ 2 = 0 := by
      have h := congrArg (algebraMap K L) hsumK
      simp only [map_add, map_one, map_pow, map_zero] at h
      rw [hωL]
      exact h
    have hωL3 : ωL ^ 3 = 1 := by
      rw [hωL, ← map_pow, hω3, map_one]
    set rL : L := algebraMap K L r with hrL
    have hcrL : rL ^ 3 = a ^ 3 := by
      rw [hrL, ← map_pow, hcr, hc]
    have hrL_ne : rL ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hcrL
      exact pow_ne_zero 3 ha_ne hcrL.symm
    set x : L := a / rL with hx
    have hx3 : x ^ 3 = 1 := by
      rw [hx, div_pow, hcrL, div_self (pow_ne_zero 3 ha_ne)]
    have hfac2 : (x - 1) * (x - ωL) * (x - ωL ^ 2) = 0 := by
      have h1 : (x - 1) * (x - ωL) * (x - ωL ^ 2) = x ^ 3 - 1 := by
        have hexp : (x - 1) * (x - ωL) * (x - ωL ^ 2)
            = x ^ 3 - (1 + ωL + ωL ^ 2) * x ^ 2 + (ωL ^ 3 + ωL + ωL ^ 2) * x
              - ωL ^ 3 := by
          ring
        rw [hexp, hωL3, hsumL]
        ring
      rw [h1, hx3]
      ring
    have hxmem : x ∈ (algebraMap K L).range := by
      rcases mul_eq_zero.mp hfac2 with h | h
      · rcases mul_eq_zero.mp h with h1 | h2
        · exact ⟨1, by rw [sub_eq_zero.mp h1, map_one]⟩
        · exact ⟨ω, by rw [sub_eq_zero.mp h2, hωL]⟩
      · exact ⟨ω ^ 2, by rw [sub_eq_zero.mp h, hωL, map_pow]⟩
    obtain ⟨k, hk⟩ := hxmem
    have hxa : x * rL = a := by
      rw [hx, div_mul_cancel₀ a hrL_ne]
    exact ha ⟨k * r, by rw [map_mul, hk, ← hrL, hxa]⟩
  have hpdeg : p.natDegree = 3 := by omega
  have hdvd3 : 3 ∣ Module.finrank K L := by
    have h := minpoly.degree_dvd hpa
    rw [← hp_def, hpdeg] at h
    exact h
  exact hdvd3

end CFSG.LocalAnalysis.GLTheoremA.K1419
