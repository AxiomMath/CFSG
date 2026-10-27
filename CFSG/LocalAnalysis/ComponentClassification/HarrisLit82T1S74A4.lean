module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ADefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RS

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin
open scoped MatrixGroups

theorem sl2_eq_one_or_eq_neg_one_of_mul_self {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {M : SL(2, K)} (hM : M * M = 1) : M = 1 ∨ M = -1 := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := M.det_coe
    rwa [Matrix.det_fin_two] at h
  have hA := congrArg (fun N : SL(2, K) => (N : Matrix (Fin 2) (Fin 2) K)) hM
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hA
  have e00 := congrFun (congrFun hA 0) 0
  have e01 := congrFun (congrFun hA 0) 1
  have e10 := congrFun (congrFun hA 1) 0
  have e11 := congrFun (congrFun hA 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  by_cases htr : M 0 0 + M 1 1 = 0
  · exfalso
    apply h2
    have hd : M 1 1 = -M 0 0 := by linear_combination htr
    rw [hd] at hdet
    linear_combination -hdet - e00
  · have hb : M 0 1 = 0 := by
      have h : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp h).resolve_right htr
    have hc : M 1 0 = 0 := by
      have h : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp h).resolve_right htr
    simp only [hb, hc, mul_zero, add_zero, zero_add, sub_zero] at e00 e11 hdet
    have ha0 : M 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have had : M 1 1 = M 0 0 := by
      have h : M 0 0 * (M 1 1 - M 0 0) = 0 := by linear_combination hdet - e00
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ha0)
    have hpm : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination e00
    rcases mul_eq_zero.mp hpm with h | h
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, had, sub_eq_zero.mp h]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, had, eq_neg_of_add_eq_zero_left h]

theorem a4_holds : A4 := by
  intro K _ _ hodd
  have h2 : (2 : K) ≠ 0 := Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true with hρ
  have hinj : Function.Injective ρ := longSL2_injective _ fin3_zero_ne_one true true
  refine ⟨fun x hx hxx => ?_, fun P hPle hP2 hPidx => ?_⟩
  · obtain ⟨M, rfl⟩ := hx
    have hMM : M * M = 1 := hinj (by rw [map_mul, hxx, map_one])
    rcases sl2_eq_one_or_eq_neg_one_of_mul_self h2 hMM with rfl | rfl
    · exact Or.inl (map_one ρ)
    · exact Or.inr rfl
  · have hP'2 : IsPGroup 2 (P.comap ρ) := hP2.comap_of_injective ρ hinj
    have hidx : ¬ 2 ∣ (P.comap ρ).index := by
      rw [index_comap]
      exact hPidx
    have hSP : ((hP'2.toSylow hidx : Sylow 2 SL(2, K)) : Subgroup SL(2, K)) = P.comap ρ :=
      IsPGroup.toSylow_coe hP'2 hidx
    obtain ⟨-, x, hx, y, hy, hxx, hyy, hxy⟩ := sylow_sl2_facts hodd (hP'2.toSylow hidx)
    rw [hSP] at hx hy
    refine ⟨⟨ρ x, hx, ρ y, hy, ?_, ?_, fun h => hxy (hinj (by rw [map_mul, map_mul]; exact h))⟩,
      fun w hw hwP => ?_⟩
    · rw [← map_mul, hxx]
    · rw [← map_mul, hyy]
    · obtain ⟨M, rfl⟩ := hw
      obtain ⟨c, hc⟩ := eq_smul_one_of_commute_sylow_sl2 hodd (hP'2.toSylow hidx)
        (M := (M : Matrix (Fin 2) (Fin 2) K)) (by
          intro g hg
          rw [hSP] at hg
          have hMg : M * g = g * M := hinj (by rw [map_mul, map_mul]; exact hwP (ρ g) hg)
          exact congrArg (fun N : SL(2, K) => (N : Matrix (Fin 2) (Fin 2) K)) hMg)
      have hc2 : c * c = 1 := by
        have h := M.det_coe
        rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, pow_two] at h
        exact h
      have hMM : M * M = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.SpecialLinearGroup.coe_one,
          smul_mul_smul_comm, one_mul, hc2, one_smul]
      rcases sl2_eq_one_or_eq_neg_one_of_mul_self h2 hMM with rfl | rfl
      · exact Or.inl (map_one ρ)
      · exact Or.inr rfl

end CFSG.ComponentClassification.HarrisLit.T1.S74
