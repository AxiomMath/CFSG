module

public import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeL44

public noncomputable section

namespace CFSG.EvenSporadicStandard.M24Std

namespace L44Atlas

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.KS21.L44 (F4 M PL center_M center_PL)

abbrev unitMat (i j : Fin 4) : Matrix (Fin 4) (Fin 4) F4 := single i j 1

theorem scalars_F4 : scalars 4 F4 = ⊥ := (scalars_eq_center 4 F4).trans center_M

theorem proj_injective_F4 : Function.Injective (proj 4 F4) :=
  (MonoidHom.ker_eq_bot_iff _).mp (by rw [ker_proj, scalars_F4])

theorem map_transvection (ρ : F4 ≃+* F4) {i j : Fin 4} (h : i ≠ j) (c : F4) :
    Matrix.SpecialLinearGroup.map ρ.toRingHom (Matrix.SpecialLinearGroup.transvection h c) =
      Matrix.SpecialLinearGroup.transvection h (ρ c) := by
  apply Subtype.ext
  ext a b
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  split_ifs <;> simp_all

theorem transvection_inv_transpose {i j : Fin 4} (h : i ≠ j) :
    (Matrix.SpecialLinearGroup.transvection h (1 : F4))⁻¹.transpose =
      Matrix.SpecialLinearGroup.transvection h.symm (1 : F4) := by
  have h1 : (Matrix.SpecialLinearGroup.transvection h (1 : F4))⁻¹ =
      Matrix.SpecialLinearGroup.transvection h (-1) :=
    inv_eq_of_mul_eq_one_right (Matrix.SpecialLinearGroup.transvection_mul_neg h 1)
  rw [h1]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, CharTwo.neg_eq]

theorem commute_single_of_conj_eq {x : M} {i j : Fin 4} (h : i ≠ j)
    (hx : x * Matrix.SpecialLinearGroup.transvection h (1 : F4) * x⁻¹ =
      Matrix.SpecialLinearGroup.transvection h (1 : F4)) :
    Commute (unitMat i j) (x : Matrix (Fin 4) (Fin 4) F4) := by
  rw [mul_inv_eq_iff_eq_mul] at hx
  have h3 := congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4)) hx
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    mul_add, add_mul, mul_one, one_mul] at h3
  exact (add_left_cancel h3).symm

theorem eq_one_of_conj_eq_map (ρ : F4 ≃+* F4) (x : M)
    (h : ∀ g : M, x * g * x⁻¹ = Matrix.SpecialLinearGroup.map ρ.toRingHom g) : ρ = 1 := by
  have hcomm : Pairwise fun i j : Fin 4 => Commute (unitMat i j)
      (x : Matrix (Fin 4) (Fin 4) F4) := fun i j hij =>
    commute_single_of_conj_eq hij
      ((h _).trans (by rw [map_transvection, map_one]))
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_single hcomm
  have hdet : r ^ 4 = 1 := by
    have := x.2
    rw [← hr, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at this
    exact this
  have hx : x ∈ Subgroup.center M :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨r, by rwa [Fintype.card_fin], hr⟩
  rw [center_M, Subgroup.mem_bot] at hx
  subst hx
  refine RingEquiv.ext fun c => ?_
  have h1 := congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4) 0 1)
    (h (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 1) c))
  simp only [one_mul, inv_one, mul_one, map_transvection] at h1
  simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply] using h1.symm

theorem false_of_conj_eq_map_dual (ρ : F4 ≃+* F4) (x : M)
    (h : ∀ g : M, x * g * x⁻¹ =
      Matrix.SpecialLinearGroup.map ρ.toRingHom ((g⁻¹).transpose)) : False := by
  have key : ∀ {i j : Fin 4}, i ≠ j →
      (x : Matrix (Fin 4) (Fin 4) F4) * unitMat i j =
        unitMat j i * (x : Matrix (Fin 4) (Fin 4) F4) := by
    intro i j hij
    have h1 := h (Matrix.SpecialLinearGroup.transvection hij (1 : F4))
    rw [transvection_inv_transpose, map_transvection, map_one, mul_inv_eq_iff_eq_mul] at h1
    have h3 := congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4)) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      mul_add, add_mul, mul_one, one_mul] at h3
    exact add_left_cancel h3
  have h01 := key (by decide : (0 : Fin 4) ≠ 1)
  have h12 := key (by decide : (1 : Fin 4) ≠ 2)
  have h02 := key (by decide : (0 : Fin 4) ≠ 2)
  have h0 : unitMat 2 0 * (x : Matrix (Fin 4) (Fin 4) F4) = 0 := by
    have e02 : unitMat 0 2 = unitMat 0 1 * unitMat 1 2 := by simp [unitMat]
    have e10 : unitMat 1 0 * unitMat 2 1 = 0 :=
      Matrix.single_mul_single_of_ne (1 : F4) (1 : Fin 4) (0 : Fin 4) (2 : Fin 4)
        (by decide : (0 : Fin 4) ≠ 2) (1 : F4)
    calc unitMat 2 0 * (x : Matrix (Fin 4) (Fin 4) F4)
        = (x : Matrix (Fin 4) (Fin 4) F4) * unitMat 0 2 := h02.symm
      _ = (x : Matrix (Fin 4) (Fin 4) F4) * (unitMat 0 1 * unitMat 1 2) := by rw [e02]
      _ = ((x : Matrix (Fin 4) (Fin 4) F4) * unitMat 0 1) * unitMat 1 2 := by
          rw [Matrix.mul_assoc]
      _ = unitMat 1 0 * ((x : Matrix (Fin 4) (Fin 4) F4) * unitMat 1 2) := by
          rw [h01, Matrix.mul_assoc]
      _ = (unitMat 1 0 * unitMat 2 1) * (x : Matrix (Fin 4) (Fin 4) F4) := by
          rw [h12, ← Matrix.mul_assoc]
      _ = 0 := by rw [e10, zero_mul]
  have hrow : ∀ b, (x : Matrix (Fin 4) (Fin 4) F4) 0 b = 0 := fun b => by
    have := congrFun₂ h0 2 b
    simpa using this
  have hdet := Matrix.det_eq_zero_of_row_eq_zero (0 : Fin 4) hrow
  rw [x.2] at hdet
  exact one_ne_zero hdet

@[expose] def dpow (b : Bool) : MulAut PL := if b then dualAut 4 F4 else 1

theorem dpow_false : dpow false = 1 := rfl

theorem dualAut_mul_self : dualAut 4 F4 * dualAut 4 F4 = 1 :=
  (standard_automorphism_transport (K := F4) (n := 4)).2.2.2.1

theorem dualAut_comm (σ : F4 ≃+* F4) :
    dualAut 4 F4 * fieldAut 4 F4 σ = fieldAut 4 F4 σ * dualAut 4 F4 := by
  have h := (standard_automorphism_transport (K := F4) (n := 4)).2.2.2.2.2.1 σ
  calc dualAut 4 F4 * fieldAut 4 F4 σ
      = dualAut 4 F4 * fieldAut 4 F4 σ * (dualAut 4 F4 * dualAut 4 F4) := by
        rw [dualAut_mul_self, mul_one]
    _ = (dualAut 4 F4 * fieldAut 4 F4 σ * dualAut 4 F4) * dualAut 4 F4 := by
        simp only [mul_assoc]
    _ = fieldAut 4 F4 σ * dualAut 4 F4 := by rw [h]

theorem dpow_mul (b c : Bool) : dpow b * dpow c = dpow (xor b c) := by
  cases b <;> cases c <;> simp [dpow, dualAut_mul_self]

theorem dpow_comm (b : Bool) (σ : F4 ≃+* F4) :
    dpow b * fieldAut 4 F4 σ = fieldAut 4 F4 σ * dpow b := by
  cases b <;> simp [dpow, dualAut_comm]

theorem eq_of_mem_range (ρ : F4 ≃+* F4) (b : Bool)
    (h : fieldAut 4 F4 ρ * dpow b ∈ (MulAut.conj : PL →* MulAut PL).range) :
    ρ = 1 ∧ b = false := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨x, rfl⟩ := proj_surjective 4 F4 y
  have hg : ∀ g : M, (MulAut.conj (proj 4 F4 x)) (proj 4 F4 g) =
      (fieldAut 4 F4 ρ * dpow b) (proj 4 F4 g) := fun g => by rw [hy]
  have hconj : ∀ g : M, (MulAut.conj (proj 4 F4 x)) (proj 4 F4 g) = proj 4 F4 (x * g * x⁻¹) :=
    fun g => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  cases b
  · refine ⟨eq_one_of_conj_eq_map ρ x fun g => proj_injective_F4 ?_, rfl⟩
    rw [← hconj, hg, dpow_false, mul_one, fieldAut_proj]
  · exfalso
    refine false_of_conj_eq_map_dual ρ x fun g => proj_injective_F4 ?_
    rw [← hconj, hg, MulAut.mul_apply]
    change fieldAut 4 F4 ρ (dualAut 4 F4 (proj 4 F4 g)) = _
    rw [dualAut_proj, fieldAut_proj]

end L44Atlas

end CFSG.EvenSporadicStandard.M24Std
