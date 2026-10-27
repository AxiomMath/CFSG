module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Sym

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

open Matrix Finset CFSG.Open CFSG.LocalAnalysis.ComponentInitial

open scoped Classical

variable {p f : ℕ} {K : Type} [Field K]

theorem dagI_inv_unitary (h : UnitaryFieldData p f K) {R : GL (Fin 7) K}
    (hR : dagI h (R : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K) = 1) :
    dagI h ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
      ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = 1 := by
  have hRi : ((R : Matrix (Fin 7) (Fin 7) K))⁻¹ = dagI h (R : Matrix (Fin 7) (Fin 7) K) :=
    Matrix.inv_eq_left_inv hR
  have hdet : IsUnit (R : Matrix (Fin 7) (Fin 7) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp R.isUnit
  have key : dagI h ((R : Matrix (Fin 7) (Fin 7) K))⁻¹ = (R : Matrix (Fin 7) (Fin 7) K) := by
    rw [hRi, dagI_dagI]
  rw [Matrix.coe_units_inv, key]
  exact Matrix.mul_nonsing_inv _ hdet

theorem conj_unitary_mat (h : UnitaryFieldData p f K) {R : GL (Fin 7) K}
    (hR : dagI h (R : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K) = 1)
    {X : Matrix (Fin 7) (Fin 7) K} (hX : dagI h X * X = 1) :
    dagI h (((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * X *
        (R : Matrix (Fin 7) (Fin 7) K)) *
      (((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * X *
        (R : Matrix (Fin 7) (Fin 7) K)) = 1 := by
  have hdet : IsUnit (R : Matrix (Fin 7) (Fin 7) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp R.isUnit
  set Rm : Matrix (Fin 7) (Fin 7) K := (R : Matrix (Fin 7) (Fin 7) K) with hRm
  set Rim : Matrix (Fin 7) (Fin 7) K := ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) with hRim_def
  have hRim : Rim = dagI h Rm := by
    rw [hRim_def, Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hR
  have hRRi : Rm * Rim = 1 := by
    rw [hRim_def, Matrix.coe_units_inv]
    exact Matrix.mul_nonsing_inv _ hdet
  have hRiR : Rim * Rm = 1 := by
    rw [hRim_def, Matrix.coe_units_inv]
    exact Matrix.nonsing_inv_mul _ hdet
  have hdagRim : dagI h Rim = Rm := by
    rw [hRim, dagI_dagI]
  have hdagRm : dagI h Rm = Rim := hRim.symm
  rw [dagI_mul, dagI_mul, hdagRm, hdagRim]
  have e1 : Rim * (dagI h X * Rm) * (Rim * X * Rm) = Rim * dagI h X * (Rm * Rim) * X * Rm := by
    simp only [Matrix.mul_assoc]
  rw [e1, hRRi, Matrix.mul_one]
  have e2 : Rim * dagI h X * X * Rm = Rim * (dagI h X * X) * Rm := by
    simp only [Matrix.mul_assoc]
  rw [e2, hX, Matrix.mul_one, hRiR]

theorem conj_mem (h : UnitaryFieldData p f K) {R : GL (Fin 7) K}
    (hR : dagI h (R : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K) = 1)
    {x : GL (Fin 7) K} (hx : x ∈ StatedSU 7 (p ^ f) K) :
    R⁻¹ * x * R ∈ StatedSU 7 (p ^ f) K := by
  obtain ⟨hdet, hu⟩ := (mem_statedSU_iff h 7 x).mp hx
  have hdetR : IsUnit (R : Matrix (Fin 7) (Fin 7) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp R.isUnit
  rw [mem_statedSU_iff h 7]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.coe_units_inv,
      Matrix.det_nonsing_inv, hdet, mul_one, Ring.inverse_mul_cancel _ hdetR]
  · exact conj_unitary_mat h hR hu

theorem conjS_left_inv (R x : GL (Fin 7) K) : R * (R⁻¹ * x * R) * R⁻¹ = x := by group

theorem conjS_right_inv (R x : GL (Fin 7) K) : R⁻¹ * (R * x * R⁻¹) * R = x := by group

theorem conjS_mul (R x y : GL (Fin 7) K) :
    R⁻¹ * (x * y) * R = (R⁻¹ * x * R) * (R⁻¹ * y * R) := by group

@[expose] noncomputable def conjS (h : UnitaryFieldData p f K) {R : GL (Fin 7) K}
    (hR : dagI h (R : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K) = 1) :
    ↥(StatedSU 7 (p ^ f) K) ≃* ↥(StatedSU 7 (p ^ f) K) where
  toFun x := ⟨R⁻¹ * x * R, conj_mem h hR x.2⟩
  invFun y := ⟨R * y * R⁻¹, by
    simpa only [inv_inv] using conj_mem h (dagI_inv_unitary h hR) y.2⟩
  left_inv x := Subtype.ext (conjS_left_inv R x)
  right_inv y := Subtype.ext (conjS_right_inv R y)
  map_mul' x y := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    exact conjS_mul R _ _)

theorem conjS_apply (h : UnitaryFieldData p f K) {R : GL (Fin 7) K}
    (hR : dagI h (R : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K) = 1)
    (x : ↥(StatedSU 7 (p ^ f) K)) : ((conjS h hR x : ↥(StatedSU 7 (p ^ f) K)) : GL (Fin 7) K) =
      R⁻¹ * (x : GL (Fin 7) K) * R :=
  rfl

theorem conj_scalar {R : GL (Fin 7) K} {x : GL (Fin 7) K} (hx : x ∈ StatedScalars (Fin 7) K) :
    R⁻¹ * x * R = x := by
  have hc : R * x = x * R := by
    have hcen : x ∈ Subgroup.center (GL (Fin 7) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hx
    exact Subgroup.mem_center_iff.mp hcen R
  calc R⁻¹ * x * R = R⁻¹ * (x * R) := by rw [mul_assoc]
    _ = R⁻¹ * (R * x) := by rw [hc]
    _ = x := by rw [inv_mul_cancel_left]

theorem scalars_map_conjS (h : UnitaryFieldData p f K) {R : GL (Fin 7) K}
    (hR : dagI h (R : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K) = 1) :
    ((StatedScalars (Fin 7) K).subgroupOf (StatedSU 7 (p ^ f) K)).map (conjS h hR).toMonoidHom =
      (StatedScalars (Fin 7) K).subgroupOf (StatedSU 7 (p ^ f) K) := by
  apply Subgroup.ext
  intro y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [Subgroup.mem_subgroupOf] at hx
    rw [← hxy, Subgroup.mem_subgroupOf]
    change ((conjS h hR x : ↥(StatedSU 7 (p ^ f) K)) : GL (Fin 7) K) ∈ StatedScalars (Fin 7) K
    rw [conjS_apply, conj_scalar hx]
    exact hx
  · intro hy
    refine ⟨y, hy, ?_⟩
    apply Subtype.ext
    rw [Subgroup.mem_subgroupOf] at hy
    change ((conjS h hR y : ↥(StatedSU 7 (p ^ f) K)) : GL (Fin 7) K) = (y : GL (Fin 7) K)
    rw [conjS_apply, conj_scalar hy]

@[expose] noncomputable def conjPU (h : UnitaryFieldData p f K) {R : GL (Fin 7) K}
    (hR : dagI h (R : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K) = 1) :
    StatedProj (StatedSU 7 (p ^ f) K) ≃* StatedProj (StatedSU 7 (p ^ f) K) :=
  QuotientGroup.congr ((StatedScalars (Fin 7) K).subgroupOf (StatedSU 7 (p ^ f) K))
    ((StatedScalars (Fin 7) K).subgroupOf (StatedSU 7 (p ^ f) K)) (conjS h hR)
    (scalars_map_conjS h hR)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

end
