module

public import CFSG.LieType.Steinberg.CentralExt.SUThree

public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] noncomputable def normOneTorusA (u : normOne σ) : K :=
  (((u : Kˣ) : K) + (((u : Kˣ) : K))⁻¹) / 2

@[expose] noncomputable def normOneTorusB (u : normOne σ) : K :=
  (((u : Kˣ) : K) - (((u : Kˣ) : K))⁻¹) / 2

@[expose] noncomputable def normOneTorusMat (u : normOne σ) : Matrix (Fin 3) (Fin 3) K :=
  !![normOneTorusA u, 0, normOneTorusB u; 0, 1, 0;
     normOneTorusB u, 0, normOneTorusA u]

section NormOne

variable (u : normOne σ)

private theorem sigma_normOne_val : σ ((u : Kˣ) : K) = (((u : Kˣ) : K))⁻¹ := by
  have h := u.2
  rw [mem_normOne] at h
  exact eq_inv_of_mul_eq_one_left h

private theorem sigma_inv_normOne_val (hσ : ∀ c, σ (σ c) = c) :
    σ ((((u : Kˣ) : K))⁻¹) = ((u : Kˣ) : K) := by
  have h := congrArg σ (sigma_normOne_val u)
  rw [hσ] at h
  exact h.symm

private theorem normOneTorusA_add_normOneTorusB (h2 : (2 : K) ≠ 0) :
    normOneTorusA u + normOneTorusB u = ((u : Kˣ) : K) := by
  rw [normOneTorusA, normOneTorusB]
  field_simp
  ring

theorem normOneTorusA_one (h2 : (2 : K) ≠ 0) : normOneTorusA (1 : normOne σ) = 1 := by
  rw [normOneTorusA]
  norm_num
  exact h2

theorem normOneTorusB_one : normOneTorusB (1 : normOne σ) = 0 := by
  rw [normOneTorusB]
  simp

private theorem normOneTorusA_sq_sub_normOneTorusB_sq (h2 : (2 : K) ≠ 0) :
    normOneTorusA u ^ 2 - normOneTorusB u ^ 2 = 1 := by
  rw [normOneTorusA, normOneTorusB]
  have hu : ((u : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp
  ring

end NormOne

section Mul

variable (u v : normOne σ)

theorem normOneTorusA_mul (h2 : (2 : K) ≠ 0) :
    normOneTorusA (u * v) = normOneTorusA u * normOneTorusA v +
      normOneTorusB u * normOneTorusB v := by
  simp only [normOneTorusA, normOneTorusB, Subgroup.coe_mul, Units.val_mul]
  have hu : ((u : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hv : ((v : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp
  ring

theorem normOneTorusB_mul (h2 : (2 : K) ≠ 0) :
    normOneTorusB (u * v) = normOneTorusA u * normOneTorusB v +
      normOneTorusB u * normOneTorusA v := by
  simp only [normOneTorusA, normOneTorusB, Subgroup.coe_mul, Units.val_mul]
  have hu : ((u : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hv : ((v : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp
  ring

end Mul

section Matrix

variable (u : normOne σ)

private theorem sigma_normOneTorusA (hσ : ∀ c, σ (σ c) = c) :
    σ (normOneTorusA u) = normOneTorusA u := by
  have h2σ : σ (2 : K) = 2 := by simpa using map_ofNat σ 2
  rw [normOneTorusA, map_div₀, map_add, sigma_normOne_val,
    sigma_inv_normOne_val u hσ, h2σ]
  ring

private theorem sigma_normOneTorusB (hσ : ∀ c, σ (σ c) = c) :
    σ (normOneTorusB u) = -normOneTorusB u := by
  have h2σ : σ (2 : K) = 2 := by simpa using map_ofNat σ 2
  rw [normOneTorusB, map_div₀, map_sub, sigma_normOne_val,
    sigma_inv_normOne_val u hσ, h2σ]
  ring

private theorem conjTr_normOneTorusMat (hσ : ∀ c, σ (σ c) = c) :
    conjTr σ (normOneTorusMat u) =
      !![normOneTorusA u, 0, -normOneTorusB u; 0, 1, 0;
         -normOneTorusB u, 0, normOneTorusA u] := by
  have h2σ : σ (2 : K) = 2 := by simpa using map_ofNat σ 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, normOneTorusMat, sigma_normOneTorusA u hσ, sigma_normOneTorusB u hσ,
      h2σ, map_ofNat, map_natCast]

theorem conjTr_normOneTorusMat_mul_self (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0) :
    conjTr σ (normOneTorusMat u) * normOneTorusMat u = 1 := by
  rw [conjTr_normOneTorusMat u hσ]
  have h := normOneTorusA_sq_sub_normOneTorusB_sq u h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normOneTorusMat, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals try rfl
  all_goals try ring
  all_goals linear_combination h

theorem det_normOneTorusMat (h2 : (2 : K) ≠ 0) : (normOneTorusMat u).det = 1 := by
  rw [Matrix.det_fin_three]
  have h := normOneTorusA_sq_sub_normOneTorusB_sq u h2
  simp [normOneTorusMat]
  linear_combination h

theorem det_normOneTorusMat_ne_zero (h2 : (2 : K) ≠ 0) :
    (normOneTorusMat u).det ≠ 0 := by
  rw [det_normOneTorusMat u h2]
  exact one_ne_zero

@[expose] noncomputable def normOneTorusElt (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0) :
    SUid σ 3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (normOneTorusMat u)
      (det_normOneTorusMat_ne_zero u h2),
    by
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact det_normOneTorusMat u h2,
    by
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact conjTr_normOneTorusMat_mul_self u hσ h2⟩

theorem coe_normOneTorusElt (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0) :
    ((normOneTorusElt (σ := σ) u hσ h2 : SUid σ 3) : GL (Fin 3) K) =
      Matrix.GeneralLinearGroup.mkOfDetNeZero (normOneTorusMat u)
        (det_normOneTorusMat_ne_zero u h2) := rfl

end Matrix

@[expose] noncomputable def normOneTorusHom (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0) :
    normOne σ →* SUid σ 3 where
  toFun u := normOneTorusElt u hσ h2
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_normOneTorusElt]
    change normOneTorusMat 1 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [normOneTorusMat, normOneTorusA_one h2, normOneTorusB_one]
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_normOneTorusElt, coe_normOneTorusElt,
      coe_normOneTorusElt]
    change normOneTorusMat (u * v) =
      Matrix.GeneralLinearGroup.mkOfDetNeZero (normOneTorusMat u)
          (det_normOneTorusMat_ne_zero u h2) *
        Matrix.GeneralLinearGroup.mkOfDetNeZero (normOneTorusMat v)
          (det_normOneTorusMat_ne_zero v h2)
    rw [← Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [normOneTorusMat, Matrix.mul_apply, Fin.sum_univ_three,
        normOneTorusA_mul u v h2, normOneTorusB_mul u v h2] <;> ring

private theorem coe_normOneTorusHom (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0)
    (u : normOne σ) :
    ((normOneTorusHom (σ := σ) hσ h2 u : SUid σ 3) : GL (Fin 3) K) =
      Matrix.GeneralLinearGroup.mkOfDetNeZero (normOneTorusMat u)
        (det_normOneTorusMat_ne_zero u h2) := rfl

theorem coe_coe_normOneTorusHom (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0)
    (u : normOne σ) :
    ((((normOneTorusHom (σ := σ) hσ h2 u : SUid σ 3) : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) = normOneTorusMat u := by
  rw [coe_normOneTorusHom]
  exact Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem normOneTorusHom_injective (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0) :
    Function.Injective (normOneTorusHom (σ := σ) hσ h2) := by
  intro u v huv
  have hmat : normOneTorusMat u = normOneTorusMat v := by
    have h := congrArg (fun w : SUid σ 3 =>
      (((w : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) huv
    rw [coe_coe_normOneTorusHom hσ h2 u, coe_coe_normOneTorusHom hσ h2 v] at h
    exact h
  have hb : normOneTorusB u = normOneTorusB v := by
    have := congrFun (congrFun hmat 0) 2
    simpa [normOneTorusMat] using this
  have ha : normOneTorusA u = normOneTorusA v := by
    have := congrFun (congrFun hmat 0) 0
    simpa [normOneTorusMat] using this
  apply Subtype.ext
  apply Units.ext
  rw [← normOneTorusA_add_normOneTorusB u h2,
    ← normOneTorusA_add_normOneTorusB v h2, ha, hb]

section ConjSign

variable (u : normOne σ)

theorem normOneTorusMat_conj_sign₃ (hσ : ∀ c, σ (σ c) = c) :
    Matrix.diagonal (![(-1 : K), -1, 1]) * normOneTorusMat u *
        Matrix.diagonal (![(-1 : K), -1, 1]) = normOneTorusMat (u⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normOneTorusMat, normOneTorusA, normOneTorusB, Matrix.mul_apply,
      Fin.sum_univ_three, Units.val_inv_eq_inv_val] <;>
    ring

end ConjSign

section FieldMap

variable (φ : K ≃+* K) (hφ : ∀ c, φ (σ c) = σ (φ c))

@[expose] noncomputable def normOneMap : normOne σ →* normOne σ where
  toFun u := ⟨Units.map (φ : K →* K) u, by
    rw [mem_normOne]
    change σ (φ ((u : Kˣ) : K)) * φ ((u : Kˣ) : K) = 1
    rw [← hφ ((u : Kˣ) : K), ← map_mul, u.2, map_one]⟩
  map_one' := Subtype.ext (Units.ext (map_one (φ : K →* K)))
  map_mul' u v := Subtype.ext (Units.ext (map_mul (φ : K →* K) ((u : Kˣ) : K) ((v : Kˣ) : K)))

theorem coe_coe_normOneMap (u : normOne σ) :
    (((normOneMap φ hφ u : normOne σ) : Kˣ) : K) = φ ((u : Kˣ) : K) := rfl

end FieldMap

end CFSG.ClassicalGroups.Unitary
