module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.Arith
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Open
open CFSG.HardMathSupport.Foote.ModuleExclusions (fixF mem_fixF Ai speiser)

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Finite F]

@[expose] noncomputable def liftGL (σ : F ≃+* F) : GL (Fin 3) (fixF σ) →* GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.map (fixF σ).subtype

theorem coe_liftGL (σ : F ≃+* F) (M : GL (Fin 3) (fixF σ)) (i j : Fin 3) :
    ((liftGL σ M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j = (M i j : fixF σ) := rfl

theorem liftGL_injective (σ : F ≃+* F) : Function.Injective (liftGL σ) := by
  intro A B h
  apply Units.ext
  ext i j
  have := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) i j) h
  exact this

noncomputable abbrev mapσ (σ : F ≃+* F) : GL (Fin 3) F →* GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.map (σ : F →+* F)

theorem mapσ_liftGL (σ : F ≃+* F) (M : GL (Fin 3) (fixF σ)) : mapσ σ (liftGL σ M) = liftGL σ M := by
  apply Units.ext
  ext i j
  change σ ((M i j : fixF σ) : F) = _
  exact mem_fixF.1 (M i j).2

theorem exists_liftGL (σ : F ≃+* F) {M : GL (Fin 3) F} (h : mapσ σ M = M) :
    ∃ M₀ : GL (Fin 3) (fixF σ), liftGL σ M₀ = M := by
  have hv : ∀ N : GL (Fin 3) F, mapσ σ N = N → ∀ i j, (N : Matrix (Fin 3) (Fin 3) F) i j ∈ fixF σ := by
    intro N hN i j
    have := congrArg (fun K : GL (Fin 3) F => (K : Matrix (Fin 3) (Fin 3) F) i j) hN
    exact mem_fixF.2 this
  have hMi : mapσ σ M⁻¹ = M⁻¹ := by rw [map_inv, h]
  let A : Matrix (Fin 3) (Fin 3) (fixF σ) := Matrix.of fun i j => ⟨_, hv M h i j⟩
  let B : Matrix (Fin 3) (Fin 3) (fixF σ) := Matrix.of fun i j => ⟨_, hv M⁻¹ hMi i j⟩
  have hA : A.map (fixF σ).subtype = (M : Matrix (Fin 3) (Fin 3) F) := by ext i j; rfl
  have hB : B.map (fixF σ).subtype = ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    ext i j; rfl
  have hAB : A * B = 1 := by
    refine Matrix.map_injective (f := (fixF σ).subtype) Subtype.val_injective ?_
    show (A * B).map (fixF σ).subtype = (1 : Matrix (Fin 3) (Fin 3) (fixF σ)).map (fixF σ).subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : B * A = 1 := by
    refine Matrix.map_injective (f := (fixF σ).subtype) Subtype.val_injective ?_
    show (B * A).map (fixF σ).subtype = (1 : Matrix (Fin 3) (Fin 3) (fixF σ)).map (fixF σ).subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

theorem fieldAut_mul_conjAut_lift (σ : F ≃+* F) (M : GL (Fin 3) (fixF σ)) :
    fieldAut 3 F σ * conjAut 3 F (liftGL σ M) = conjAut 3 F (liftGL σ M) * fieldAut 3 F σ := by
  rw [fieldAut_mul_conjAut, mapσ_liftGL]

theorem mapσ_scalar (σ : F ≃+* F) (u : Fˣ) :
    mapσ σ (Matrix.GeneralLinearGroup.scalar (Fin 3) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : F →* F) u) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem mapσ_cube (σ : F ≃+* F) (hσ : σ ^ 3 = 1) (A : GL (Fin 3) F) :
    mapσ σ (mapσ σ (mapσ σ A)) = A := by
  apply Units.ext
  ext i j
  change σ (σ (σ ((A : Matrix (Fin 3) (Fin 3) F) i j))) = _
  have := congrArg (fun τ : F ≃+* F => τ ((A : Matrix (Fin 3) (Fin 3) F) i j)) hσ
  simpa [pow_succ, RingAut.mul_apply] using this

theorem exists_liftGL_of_commute {σ : F ≃+* F} (hσ : orderOf σ = 3) {a : MulAut (projectiveSL 3 F)}
    (ha : a ∈ linearAutGroup 3 F) (hc : fieldAut 3 F σ * a = a * fieldAut 3 F σ) :
    ∃ M₀ : GL (Fin 3) (fixF σ), a = conjAut 3 F (liftGL σ M₀) := by
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨A₀, rfl⟩ := mem_linearAutGroup_iff.1 ha
  rw [fieldAut_mul_conjAut] at hc
  have hc' : conjAut 3 F (mapσ σ A₀) = conjAut 3 F A₀ := mul_right_cancel hc
  have hk : conjAut 3 F (mapσ σ A₀ * A₀⁻¹) = 1 := by
    rw [map_mul, hc', map_inv, mul_inv_cancel]
  obtain ⟨u, hu⟩ := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).1 hk
  have hmat : mapσ σ A₀ = Matrix.GeneralLinearGroup.scalar (Fin 3) u * A₀ := by
    rw [← hu, inv_mul_cancel_right]
  have hN : (u : F) * σ u * σ (σ u) = 1 := by
    have h1 : mapσ σ (mapσ σ (mapσ σ A₀)) = A₀ := mapσ_cube σ hσ3 A₀
    have e1 : mapσ σ (mapσ σ A₀) = Matrix.GeneralLinearGroup.scalar (Fin 3)
        (Units.map (σ : F →* F) u) * (Matrix.GeneralLinearGroup.scalar (Fin 3) u * A₀) := by
      rw [hmat, map_mul, mapσ_scalar, hmat]
    have e2 : mapσ σ (mapσ σ (mapσ σ A₀)) = Matrix.GeneralLinearGroup.scalar (Fin 3)
        (Units.map (σ : F →* F) (Units.map (σ : F →* F) u) * Units.map (σ : F →* F) u * u) * A₀ := by
      rw [e1, map_mul, mapσ_scalar, map_mul, mapσ_scalar, hmat, map_mul, map_mul]
      simp only [mul_assoc]
    rw [e2] at h1
    have h3 : Matrix.GeneralLinearGroup.scalar (Fin 3)
        (Units.map (σ : F →* F) (Units.map (σ : F →* F) u) * Units.map (σ : F →* F) u * u) = 1 := by
      have := congrArg (· * A₀⁻¹) h1
      simpa using this
    have h4 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 0 0) h3
    simp [Matrix.GeneralLinearGroup.scalar] at h4
    linear_combination h4
  have hAi : Ai σ (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (((u⁻¹ : Fˣ)) : F)) 3 = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp [Ai, Matrix.mul_apply]
    have hu0 : (u : F) ≠ 0 := u.ne_zero
    have hσu0 : σ (u : F) ≠ 0 := by simp [hu0]
    have hσσu0 : σ (σ (u : F)) ≠ 0 := by simp [hu0]
    field_simp
    linear_combination (-1 : F) * hN
  obtain ⟨B, hBdet, hB⟩ := speiser σ (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (((u⁻¹ : Fˣ)) : F)) 3
    hσ (by norm_num) hAi
  set b : F := B 0 0 with hb
  have hb0 : b ≠ 0 := by
    intro h0
    apply hBdet
    rw [Matrix.det_unique]
    simpa [hb] using h0
  have hbσ : (u : F)⁻¹ * σ b = b := by
    have := congrFun (congrFun hB 0) 0
    simpa [Matrix.mul_apply, hb] using this
  set m : Fˣ := Units.mk0 b⁻¹ (inv_ne_zero hb0) with hm
  have hmσ : Units.map (σ : F →* F) m * u = m := by
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, hm,
      Units.val_mk0, map_inv₀]
    have hu0 : (u : F) ≠ 0 := u.ne_zero
    have : σ b = (u : F) * b := by
      field_simp at hbσ
      linear_combination hbσ
    rw [this]
    field_simp
  have hfix : mapσ σ (Matrix.GeneralLinearGroup.scalar (Fin 3) m * A₀) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) m * A₀ := by
    rw [map_mul, mapσ_scalar, hmat, ← mul_assoc, ← map_mul, hmσ]
  obtain ⟨M₀, hM₀⟩ := exists_liftGL σ hfix
  refine ⟨M₀, ?_⟩
  rw [hM₀, map_mul, conjAut_scalar, one_mul]

end CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
