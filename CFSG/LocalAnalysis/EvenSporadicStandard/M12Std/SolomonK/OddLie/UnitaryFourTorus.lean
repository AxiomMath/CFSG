module

public import CFSG.GH74.Filter.ClassicalOdd.Unitary

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open CFSG.GH74.Filter.ClassicalOdd CFSG.SectionRank.ClassicalOdd Matrix

section Torus

variable {K : Type} [Field K]

@[expose] def torusMat (u x y : K) : Matrix (Fin 2) (Fin 2) K :=
  !![(x + y) / 2, u⁻¹ * (x - y) / 2; u * (x - y) / 2, (x + y) / 2]

theorem torusMat_mul {u : K} (h2 : (2 : K) ≠ 0) (hu : u ≠ 0) (x y x' y' : K) :
    torusMat u x y * torusMat u x' y' = torusMat u (x * x') (y * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem torusMat_one {u : K} (h2 : (2 : K) ≠ 0) : torusMat u 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMat, Matrix.one_apply, one_add_one_eq_two, h2]

theorem det_torusMat {u : K} (h2 : (2 : K) ≠ 0) (hu : u ≠ 0) (x y : K) :
    (torusMat u x y).det = x * y := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  rw [Matrix.det_fin_two]
  simp only [torusMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  ring

theorem torusMat_inj {u x y x' y' : K} (h2 : (2 : K) ≠ 0) (hu : u ≠ 0)
    (h : torusMat u x y = torusMat u x' y') : x = x' ∧ y = y' := by
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp only [torusMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h10
  have hsum : x + y = x' + y' := (div_left_inj' h2).1 h00
  have hdiff : x - y = x' - y' := mul_left_cancel₀ hu ((div_left_inj' h2).1 h10)
  exact ⟨mul_left_cancel₀ h2 (by linear_combination hsum + hdiff),
    mul_left_cancel₀ h2 (by linear_combination hsum - hdiff)⟩

theorem isUni_aux {σ : K →+* K} {u a b : K} (hu : u ≠ 0) (hσu : σ u * u = -1)
    (h1 : σ a * a - σ b * b = 1) (h2 : σ a * b = σ b * a) :
    IsUni σ (!![a, u⁻¹ * b; u * b, a] : Matrix (Fin 2) (Fin 2) K) := by
  have hσu' : σ u = -u⁻¹ := by
    field_simp
    linear_combination hσu
  have hσuinv : σ u⁻¹ = -u := by
    rw [map_inv₀, hσu', inv_neg, inv_inv]
  have hinv : u⁻¹ * u = 1 := inv_mul_cancel₀ hu
  unfold IsUni
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hstar, Matrix.mul_apply, Fin.sum_univ_two, hσu', hσuinv, map_mul]
  · linear_combination h1 - (σ b * b) * hinv
  · linear_combination u⁻¹ * h2
  · linear_combination u * h2
  · linear_combination h1 - (σ b * b) * hinv

theorem isUni_torusMat {σ : K →+* K} {u x y : K} (h2 : (2 : K) ≠ 0) (hu : u ≠ 0)
    (hσu : σ u * u = -1) (hxy : σ x * y = 1) (hyx : σ y * x = 1) :
    IsUni σ (torusMat u x y) := by
  have hxa : σ ((x + y) / 2) = (σ x + σ y) / 2 := by rw [map_div₀, map_add, map_ofNat]
  have hxb : σ ((x - y) / 2) = (σ x - σ y) / 2 := by rw [map_div₀, map_sub, map_ofNat]
  have hT : torusMat u x y =
      !![(x + y) / 2, u⁻¹ * ((x - y) / 2); u * ((x - y) / 2), (x + y) / 2] := by
    simp [torusMat, mul_div_assoc]
  rw [hT]
  refine isUni_aux hu hσu ?_ ?_
  · rw [hxa, hxb]
    field_simp
    linear_combination 2 * hxy + 2 * hyx
  · rw [hxa, hxb]
    field_simp
    linear_combination (-2) * hxy + 2 * hyx

theorem isUni_diagonal_one {σ : K →+* K} {e : K} (he : σ e * e = 1) :
    IsUni σ (diagonal ![1, e] : Matrix (Fin 2) (Fin 2) K) := by
  unfold IsUni
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hstar, Matrix.mul_apply, Fin.sum_univ_two, he]

variable (u : K) (h2 : (2 : K) ≠ 0) (hu : u ≠ 0)

include h2 hu in
@[expose] noncomputable def torusHom : Kˣ × Kˣ →* GL (Fin 2) K :=
  MonoidHom.toHomUnits
    { toFun := fun p => torusMat u (p.1 : K) (p.2 : K)
      map_one' := by simpa using torusMat_one h2
      map_mul' := fun p q => by simpa using (torusMat_mul h2 hu _ _ _ _).symm }

theorem coe_torusHom (x y : Kˣ) :
    (torusHom u h2 hu (x, y) : Matrix (Fin 2) (Fin 2) K) = torusMat u (x : K) (y : K) :=
  rfl

theorem torusHom_injective : Function.Injective (torusHom u h2 hu) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [Prod.mk.injEq]
  have hmat : torusMat u (x : K) (y : K) = torusMat u (x' : K) (y' : K) := by
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h
    simpa [coe_torusHom] using this
  obtain ⟨hx, hy⟩ := torusMat_inj h2 hu hmat
  exact ⟨Units.ext hx, Units.ext hy⟩

theorem det_torusHom (x y : Kˣ) :
    Matrix.GeneralLinearGroup.det (torusHom u h2 hu (x, y)) = x * y := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_torusHom, det_torusMat h2 hu]

end Torus

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
