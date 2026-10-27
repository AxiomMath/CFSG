module

public import CFSG.ClassicalInvolution.RouteD.TwinYElement

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.RouteD.TwinY
open scoped MatrixGroups

section SL2

variable {F : Type*} [Field F]

theorem exists_sq_add_sq [Finite F] (hodd : Odd (Nat.card F)) (c : F) :
    ∃ a b : F, a ^ 2 + b ^ 2 = c := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C c)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by decide) _)
    (by rw [← Nat.card_eq_fintype_card]; exact Nat.odd_iff.mp hodd)
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at hab
  exact ⟨a, b, by linear_combination hab⟩

theorem sl2_diag_neg {A : Matrix (Fin 2) (Fin 2) F} (hdet : A.det = 1) (hsq : A * A = -1) :
    A 1 1 = - A 0 0 := by
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  by_contra hne
  have hne' : A 0 0 + A 1 1 ≠ 0 := fun h => hne (by linear_combination h)
  have hβ : A 0 1 = 0 := by
    have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hne'
  have hγ : A 1 0 = 0 := by
    have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hne'
  rw [hβ, hγ] at e00 e11 hdet
  have : (A 0 0 + A 1 1) ^ 2 = 0 := by linear_combination e00 + e11 + 2 * hdet
  exact hne' (pow_eq_zero_iff (by norm_num) |>.mp this)

theorem sl2_exists_anticomm (A : Matrix (Fin 2) (Fin 2) F)
    (hdet : A.det = 1) (hsq : A * A = -1) :
    ∃ N₀ : Matrix (Fin 2) (Fin 2) F, N₀.det ≠ 0 ∧ N₀ * A = -(A * N₀) := by
  have hδ : A 1 1 = - A 0 0 := sl2_diag_neg hdet hsq
  by_cases hγ : A 1 0 = 0
  · by_cases hβ : A 0 1 = 0
    · refine ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hδ, hβ, hγ]
    · refine ⟨!![A 0 1, 0; -2 * A 0 0, -A 0 1], ?_, ?_⟩
      · simp [Matrix.det_fin_two, hβ]
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, hδ, hγ] <;> ring
  · refine ⟨!![A 1 0, -2 * A 0 0; 0, -A 1 0], ?_, ?_⟩
    · simp [Matrix.det_fin_two, hγ]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hδ] <;> ring

theorem sl2_exists_conj_inv [Finite F] (hodd : Odd (Nat.card F)) (A : SL(2, F))
    (hA : A * A = -1) : ∃ N : SL(2, F), N * A * N⁻¹ = A⁻¹ := by
  have hAm : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) = -1 := by
    have := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) hA
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  have hdetA : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  obtain ⟨N₀, hN₀det, hN₀⟩ := sl2_exists_anticomm (A : Matrix (Fin 2) (Fin 2) F) hdetA hAm
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq hodd (N₀.det)⁻¹
  set P : Matrix (Fin 2) (Fin 2) F :=
    a • (1 : Matrix (Fin 2) (Fin 2) F) + b • (A : Matrix (Fin 2) (Fin 2) F) with hP
  have hPdet : P.det = a ^ 2 + b ^ 2 := by
    have hδ := sl2_diag_neg hdetA hAm
    have e00 := congrFun (congrFun hAm 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00
    rw [hP, Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
    simp [hδ]
    linear_combination (-b ^ 2) * e00
  have hMdet : (P * N₀).det = 1 := by
    rw [Matrix.det_mul, hPdet, hab]
    exact inv_mul_cancel₀ hN₀det
  let N : SL(2, F) := ⟨P * N₀, hMdet⟩
  have hinv : A⁻¹ = -A := (eq_inv_of_mul_eq_one_right (by rw [mul_neg, hA, neg_neg])).symm
  refine ⟨N, ?_⟩
  rw [hinv]
  have hPA : P * (A : Matrix (Fin 2) (Fin 2) F) = (A : Matrix (Fin 2) (Fin 2) F) * P := by
    rw [hP]
    simp [add_mul, mul_add]
  have hNA : N * A = -A * N := by
    apply Subtype.ext
    show P * N₀ * (A : Matrix (Fin 2) (Fin 2) F) = -(A : Matrix (Fin 2) (Fin 2) F) * (P * N₀)
    calc P * N₀ * (A : Matrix (Fin 2) (Fin 2) F)
        = P * (N₀ * (A : Matrix (Fin 2) (Fin 2) F)) := by rw [Matrix.mul_assoc]
      _ = P * (-((A : Matrix (Fin 2) (Fin 2) F) * N₀)) := by rw [hN₀]
      _ = -(P * (A : Matrix (Fin 2) (Fin 2) F) * N₀) := by
          rw [Matrix.mul_neg, Matrix.mul_assoc]
      _ = -((A : Matrix (Fin 2) (Fin 2) F) * P * N₀) := by rw [hPA]
      _ = -(A : Matrix (Fin 2) (Fin 2) F) * (P * N₀) := by
          rw [Matrix.neg_mul, Matrix.mul_assoc]
  calc N * A * N⁻¹ = (-A * N) * N⁻¹ := by rw [hNA]
    _ = -A := by rw [mul_assoc, mul_inv_cancel, mul_one]

end SL2

section Exact

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {K : Subgroup G} {z : G}

theorem exists_inv_conj_of_exact (hz : IsClassicalMember p f K z)
    (hex : classicalInvolutionOddCore K = ⊥) (hodd : Odd (Nat.card (GaloisField p f)))
    {a : G} (ha : a ∈ K) (haa : a * a = z) : ∃ n ∈ K, n * a * n⁻¹ = a⁻¹ := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hex
  have hzK : (⟨z, hz.mem⟩ : K) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨z, hz.mem⟩).mp
      (by rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two)
  have hA : e ⟨a, ha⟩ * e ⟨a, ha⟩ = -1 := by
    have h : (⟨a, ha⟩ : K) * ⟨a, ha⟩ = ⟨z, hz.mem⟩ := Subtype.ext haa
    rw [← map_mul, h, hzK, e.apply_symm_apply]
  obtain ⟨N, hN⟩ := sl2_exists_conj_inv hodd (e ⟨a, ha⟩) hA
  refine ⟨((e.symm N : K) : G), (e.symm N).2, ?_⟩
  have h1 : e (e.symm N * ⟨a, ha⟩ * (e.symm N)⁻¹) = e (⟨a, ha⟩⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv, e.apply_symm_apply]
    exact hN
  have h2 := e.injective h1
  exact congrArg Subtype.val h2

end Exact

end CFSG.ClassicalInvolution.RouteD.TWZ
