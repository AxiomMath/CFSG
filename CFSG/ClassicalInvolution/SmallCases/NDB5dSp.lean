module

public import CFSG.ClassicalInvolution.SmallCases.NDB5Model

public section

namespace CFSG.ClassicalInvolution.NDB.WC.Sp

open CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp CFSG.ClassicalInvolution.NDB.Model
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (QE r0 isQuasisimple_sl2)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf perfectResidual)
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.SCRSp4 (commute_longBlock_01 sq_neg_one_of_center_same
  sq_neg_one_of_center_other sp4_mul_self_eq_one_of_center neg_one_inv_SL2)
open CFSG.ClassicalInvolution.Generic (conjSub)
open scoped Matrix MatrixGroups

theorem scalar_of_commute {R : Type*} [CommRing R] {M : Matrix (Fin 2) (Fin 2) R}
    (h₁ : M * !![1, 1; 0, 1] = !![1, 1; 0, 1] * M)
    (h₂ : M * !![1, 0; 1, 1] = !![1, 0; 1, 1] * M) :
    M = M 0 0 • (1 : Matrix (Fin 2) (Fin 2) R) := by
  have e00 := congrFun (congrFun h₁ 0) 0
  have e01 := congrFun (congrFun h₁ 0) 1
  have f00 := congrFun (congrFun h₂ 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    mul_one, mul_zero, one_mul, zero_mul, add_zero] at e00 e01 f00
  have c0 : M 1 0 = 0 := by linear_combination -e00
  have d0 : M 1 1 = M 0 0 := by linear_combination -e01
  have b0 : M 0 1 = 0 := by linear_combination f00
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [c0, d0, b0]

variable {F : Type} [Field F]

@[expose] def e12 : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def e21 : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem ratM_e12 : ratM ((e12 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [ratM, e12]

theorem ratM_e21 : ratM ((e21 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [ratM, e21]

theorem eq_one_or_zneg_of_centralizes (h2 : (2 : F) ≠ 0) {lam : QE F}
    (hlam : star lam * lam = -1) {y : StatedSp 2 F} (hy2 : y * y = 1) (hyu : y * u0 F = u0 F * y)
    (hyc : ∀ B : SL(2, F), y * iota h2 hlam B = iota h2 hlam B * y) : y = 1 ∨ y = zneg F := by
  obtain ⟨N, hN, hNN⟩ := exists_unitary_of_comm y hyu
  have hcomm : ∀ B : SL(2, F), N * Xm lam B = Xm lam B * N := fun B => PhiS_injective (by
    rw [map_mul, map_mul, ← hN, ← mat_iota h2 hlam B, ← map_mul, ← map_mul, hyc B])
  have h1 := Pinv_mul_Pm h2 hlam
  have h1' := Pm_mul_Pinv h2 hlam
  set N' := Pinv F lam * N * Pm lam with hN'
  have hN'c : ∀ B : SL(2, F), N' * ratM (B : Matrix (Fin 2) (Fin 2) F) =
      ratM (B : Matrix (Fin 2) (Fin 2) F) * N' := by
    intro B
    have hB := hcomm B
    simp only [Xm] at hB
    calc N' * ratM (B : Matrix (Fin 2) (Fin 2) F)
        = Pinv F lam * (N * (Pm lam * ratM B * Pinv F lam)) * Pm lam := by
          rw [hN']
          simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = Pinv F lam * (Pm lam * ratM B * Pinv F lam * N) * Pm lam := by rw [hB]
      _ = ratM (B : Matrix (Fin 2) (Fin 2) F) * N' := by
          rw [hN']
          simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hsc := scalar_of_commute (M := N') (by rw [← ratM_e12]; exact hN'c e12)
    (by rw [← ratM_e21]; exact hN'c e21)
  set c := N' 0 0 with hc
  have hNc : N = c • (1 : Matrix (Fin 2) (Fin 2) (QE F)) := by
    calc N = Pm lam * N' * Pinv F lam := by
          rw [hN']
          simp only [← Matrix.mul_assoc, h1', Matrix.one_mul]
          simp only [Matrix.mul_assoc, h1', Matrix.mul_one]
      _ = c • (1 : Matrix (Fin 2) (Fin 2) (QE F)) := by
          rw [hsc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1']
  have hNN2 : N * N = 1 := PhiS_injective (by
    rw [map_mul, ← hN, ← map_mul, hy2, map_one, map_one])
  have hcc : c * c = 1 := by
    have := congrFun (congrFun hNN2 0) 0
    rw [hNc] at this
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have hsc' : star c * c = 1 := by
    have := congrFun (congrFun hNN 0) 0
    rw [hNc] at this
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.conjTranspose_apply]
      using this
  have hre : c.re * c.re - c.im * c.im = 1 := by
    have := congrArg QuadraticAlgebra.re hcc
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one] at this
    linear_combination this
  have hre' : c.re * c.re + c.im * c.im = 1 := by
    have := congrArg QuadraticAlgebra.re hsc'
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star] at this
    linear_combination this
  have him : c.im = 0 := by
    have h3 : (2 : F) * (c.im * c.im) = 0 := by linear_combination hre' - hre
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2)
  have hre1 : c.re * c.re = 1 := by rw [him] at hre; simpa using hre
  rcases mul_self_eq_one_iff.mp hre1 with h | h
  · left
    have hc1 : c = 1 := QuadraticAlgebra.ext (by rw [h, QuadraticAlgebra.re_one])
      (by rw [him, QuadraticAlgebra.im_one])
    apply mat_injective
    rw [hN, hNc, hc1, one_smul, map_one, map_one]
  · right
    have hc1 : c = -1 := QuadraticAlgebra.ext
      (by rw [h, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one])
      (by rw [him, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_one, neg_zero])
    apply mat_injective
    rw [hN, hNc, hc1, neg_smul, one_smul, map_neg, map_one, mat_zneg]

end CFSG.ClassicalInvolution.NDB.WC.Sp
