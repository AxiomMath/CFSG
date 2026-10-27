module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLGraphSym

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Module Matrix
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBGraphForm (isometryGroup)
open CFSG.ComponentClassification.CatalogueBLinearHigherB (matrixForm isometryGroupEquiv
  matrixForm_isAlt matrixForm_nondegenerate)

section Alt

variable {n f : ℕ} {K : Type} [Field K] [Finite K]

theorem u42_pg_card_alt (hodd : ringChar K ≠ 2) {m : ℕ} (hm : n = 2 * m) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K)) :
    Nat.card ↥(isometryGroup n K R) =
      Nat.card K ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * j) - 1) := by
  rw [← Nat.card_congr (isometryGroupEquiv R).toEquiv]
  exact CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup m (matrixForm R)
    (matrixForm_isAlt hodd R hR) (matrixForm_nondegenerate R) (by rw [Module.finrank_fin_fun, hm])

theorem u42_pg_alt_reduce (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (hn : 3 ≤ n) (hev : Even n)
    (R : GL (Fin n) K) (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K))
    {z : ℕ} (hz : ¬ 3 ∣ z) (h2 : Nat.card ↥(isometryGroup n K R) ∣ 2 * z * 25920) :
    n = 4 ∧ f = 1 ∧ Nat.card ↥(isometryGroup n K R) = 51840 := by
  have hodd := u42_ringChar_ne_two hf hK
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨n / 2, by obtain ⟨t, ht⟩ := hev; omega⟩
  have hcard := u42_pg_card_alt hodd hm R hR
  have hm2 : 2 ≤ m := by omega
  by_cases hbig : 5 ≤ f * m ^ 2
  · exfalso
    have d3 : 3 ^ (f * m ^ 2) ∣ Nat.card ↥(isometryGroup n K R) := by
      rw [hcard, hK, ← pow_mul]
      exact Dvd.intro _ rfl
    exact u42_not_three_pow_five_dvd hz (((pow_dvd_pow 3 hbig).trans d3).trans h2)
  push Not at hbig
  have hm2' : m = 2 := by
    by_contra hne
    have : 3 ≤ m := by omega
    nlinarith
  subst hm2'
  have hf1 : f = 1 := by
    have : 4 ≤ f * 2 ^ 2 := by nlinarith
    omega
  subst hf1
  have hK3 : Nat.card K = 3 := by rw [hK]; norm_num
  refine ⟨by omega, rfl, ?_⟩
  rw [hcard, hK3]
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

end Alt

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
