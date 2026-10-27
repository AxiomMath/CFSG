module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOmOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Module Matrix
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBGraphForm (isometryGroup)
open CFSG.ComponentClassification.CatalogueBLinearHigherB (matrixQuadraticForm matrixForm
  isometryGroupEquiv orthogonalGroup_matrixQuadraticForm
  polarBilin_matrixQuadraticForm_nondegenerate)
open CFSG.GroupTheory.WeirSylow

section Sym

variable {n f : ℕ} {K : Type} [Field K] [Finite K]

theorem u42_pg_card_sym (hodd : ringChar K ≠ 2) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K)) :
    Nat.card ↥(isometryGroup n K R) =
      Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm R)) :=
  (Nat.card_congr ((MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd R hR)).trans
    (isometryGroupEquiv R)).toEquiv).symm

theorem u42_not_three_dvd_of_dvd_pred {z f : ℕ} (hf : 1 ≤ f) (hz : z ∣ 3 ^ f - 1) : ¬ 3 ∣ z := by
  intro h3
  have h1 : 3 ∣ 3 ^ f - 1 := h3.trans hz
  have h2 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  have h4 : 3 ∣ 3 ^ f - (3 ^ f - 1) := Nat.dvd_sub h2 h1
  have h5 : 3 ^ f - (3 ^ f - 1) = 1 := by
    have : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
    omega
  rw [h5] at h4
  exact absurd (Nat.le_of_dvd (by norm_num) h4) (by norm_num)

theorem u42_not_three_pow_five_dvd {z : ℕ} (hz : ¬ 3 ∣ z) : ¬ 3 ^ 5 ∣ 2 * z * 25920 := by
  intro h
  have hcop : Nat.Coprime (3 ^ 5) (2 * z) := by
    refine Nat.Coprime.pow_left 5 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_)
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h3 | h3
    · norm_num at h3
    · exact hz h3
  have := hcop.dvd_of_dvd_mul_left h
  norm_num at this

theorem u42_card_orthogonalGroup_dim_three {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (hodd : ringChar K ≠ 2) {Q : QuadraticForm K W}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hm : finrank K W = 3) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
      2 * (Nat.card K : ℤ) * ((Nat.card K : ℤ) ^ 2 - 1) := by
  have := natCard_orthogonalGroup_odd hodd hQ (n := 1) hm
  rw [this]
  simp [Finset.prod_Icc_succ_top]

theorem u42_pg_symmetric_false (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (hn : 3 ≤ n)
    (R : GL (Fin n) K) (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K))
    {z : ℕ} (hzn : z ∣ n) (hzq : z ∣ Nat.card K - 1)
    (h1 : 25920 ∣ Nat.card ↥(isometryGroup n K R))
    (h2 : Nat.card ↥(isometryGroup n K R) ∣ 2 * z * 25920) : False := by
  have hodd := u42_ringChar_ne_two hf hK
  have hQ := polarBilin_matrixQuadraticForm_nondegenerate hodd R hR
  have hcard := u42_pg_card_sym hodd R hR
  have hdim : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hz3 : ¬ 3 ∣ z := u42_not_three_dvd_of_dvd_pred hf (hK ▸ hzq)
  have hzpos : 0 < z := Nat.pos_of_dvd_of_pos hzn (by omega)
  have hzle : z ≤ n := Nat.le_of_dvd (by omega) hzn
  have d3 := u42_three_pow_dvd_card_orthogonalGroup hf hK hQ hdim (by omega : 1 ≤ n)
  rw [← hcard] at d3
  by_cases hbig : 5 ≤ f * ((n - 1) ^ 2 / 4)
  · exact u42_not_three_pow_five_dvd hz3 (((pow_dvd_pow 3 hbig).trans d3).trans h2)
  push Not at hbig
  have hn5 : n ≤ 5 := by
    by_contra hlt
    have : 6 ≤ (n - 1) ^ 2 / 4 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      obtain ⟨s, rfl⟩ : ∃ s, n = s + 6 := ⟨n - 6, by omega⟩
      rw [show s + 6 - 1 = s + 5 by omega]
      nlinarith
    nlinarith
  rw [hcard] at h1 h2
  interval_cases n
  ·
    have hf4 : f ≤ 4 := by norm_num at hbig; omega
    have hfin := u42_card_orthogonalGroup_dim_three hodd hQ hdim
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm R)) = c at hfin h1 h2
    rw [hK] at hfin
    interval_cases f
    · norm_num at hfin
      have : c = 48 := by exact_mod_cast hfin
      subst this
      norm_num at h1
    · norm_num at hfin
      have : c = 1440 := by exact_mod_cast hfin
      subst this
      norm_num at h1
    · norm_num at hfin
      have : c = 39312 := by exact_mod_cast hfin
      subst this
      norm_num at h1
    · norm_num at hfin
      have : c = 1062720 := by exact_mod_cast hfin
      subst this
      have := Nat.le_of_dvd (by positivity) h2
      nlinarith
  ·
    have hf2 : f ≤ 2 := by norm_num at hbig; omega
    interval_cases f
    · have hK3 : Nat.card K = 3 := by rw [hK]; norm_num
      rcases u42_card_orthogonalGroup_three_four hK3 hQ hdim with c | c <;>
        · rw [c] at h1
          norm_num at h1
    · have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
      have hgt := u42_card_orthogonalGroup_nine_four hK9 hQ hdim
      have hle := Nat.le_of_dvd (by positivity) h2
      nlinarith
  ·
    have hf1 : f = 1 := by norm_num at hbig; omega
    subst hf1
    have hK3 : Nat.card K = 3 := by rw [hK]; norm_num
    have c := u42_card_orthogonalGroup_three_five hK3 hQ hdim
    rw [c] at h2
    have hz2 : z ∣ 2 := by rw [hK3] at hzq; exact hzq
    have hz5 : z ≤ 2 := Nat.le_of_dvd (by norm_num) hz2
    interval_cases z
    · norm_num at h2
    · norm_num at hzn

end Sym

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
