module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Member

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit
open scoped MatrixGroups

theorem two_ne_zero_of_card_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    (2 : K) ≠ 0 := by
  have h3 : (3 : K) = 0 := by
    have h := card_nsmul_eq_zero' (G := K) (x := (1 : K))
    rw [hK, Nat.smul_one_eq_cast] at h
    simpa using h
  have h21 : (2 : K) + 1 = 0 := by
    rw [show (2 : K) + 1 = 3 by norm_num, h3]
  intro h2
  rw [h2, zero_add] at h21
  exact one_ne_zero h21

theorem card_center_specialLinear_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {n : ℕ} (hn : n = 4 ∨ n = 6) : Nat.card ↥(center SL(n, K)) = 2 := by
  rcases hn with rfl | rfl
  · have h := Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 4) (R := K)
        (⟨0, by norm_num⟩ : Fin 4)).toEquiv
    rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, hK, Fintype.card_fin] at h
    norm_num at h
    exact h
  · have h := Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 6) (R := K)
        (⟨0, by norm_num⟩ : Fin 6)).toEquiv
    rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, hK, Fintype.card_fin] at h
    norm_num at h
    exact h

theorem lieModel_quotient_specialLinear {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {n : ℕ} (hn : 3 ≤ n) :
    CFSG.Blueprint.LieModel (SL(n, K) ⧸ center SL(n, K)) .PSL n 3 1 := by
  refine Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, ?_, ?_, ?_⟩,
    K, inferInstance, inferInstance, by rw [pow_one]; exact hK,
    ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K⟩⟩
  · omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

theorem blockData_specialLinear
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {n : ℕ} (hn : n = 4 ∨ n = 6) :
    BlockData SL(n, K) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
      n K (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · exact ⟨1, le_rfl, by rw [card_center_specialLinear_three hK hn, pow_one]⟩
  · exact ⟨.PSL, n, lieModel_quotient_specialLinear hK (by omega), Or.inl ⟨rfl, hn⟩⟩
  · have hL : CFSG.Blueprint.LieModel (SL(n, K) ⧸ center SL(n, K)) .PSL n 3 1 :=
      lieModel_quotient_specialLinear hK (by omega)
    have hfac := factorization_card_griessHopfMultiplier_psl
      (CFSG.ComponentClassification.TBLit.GriessMultipliersOdd.of_allModels hGA)
      (p := 3) (f := 1) (by norm_num) (by omega) hL
    have hZ := card_center_specialLinear_three hK hn
    have hgcd : Nat.gcd n (3 ^ 1 - 1) = 2 := by
      rcases hn with rfl | rfl <;> norm_num
    rw [hfac, hZ, hgcd, Nat.prime_two.factorization_self]

end CFSG.OddStandard.HigherRank.F3
