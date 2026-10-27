module

public import CFSG.GH74.GLS.Stage4.T2F1LocFA
public import CFSG.GH74.GLS.Stage4.T2F1LocH90
public import CFSG.GH74.GLS.Stage4.T2SL2B

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

theorem map_slConj {F F' : Type} [Field F] [Field F'] (φ : F →+* F') (g : GL (Fin 2) F)
    (M : SL2 F) :
    Matrix.SpecialLinearGroup.map φ (slConj g M) =
      slConj (Matrix.GeneralLinearGroup.map φ g) (Matrix.SpecialLinearGroup.map φ M) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_slConj, coe_slConj,
    Matrix.SpecialLinearGroup.map_apply_coe, ← Matrix.GeneralLinearGroup.map_inv, map_mul,
    map_mul]
  rfl

theorem exists_map_eq_smul_of_commute {F : Type} [Field F] (σ : F ≃+* F) (g : GL (Fin 2) F)
    (hcomm : ∀ M : SL2 F, Matrix.SpecialLinearGroup.map (σ : F →+* F) (slConj g M) =
      slConj g (Matrix.SpecialLinearGroup.map (σ : F →+* F) M)) :
    ∃ c : F, (g : Matrix (Fin 2) (Fin 2) F).map σ = c • (g : Matrix (Fin 2) (Fin 2) F) := by
  have h1 : ∀ N : SL2 F,
      slConj (Matrix.GeneralLinearGroup.map (σ : F →+* F) g) N = slConj g N := by
    intro N
    obtain ⟨M, rfl⟩ : ∃ M : SL2 F, Matrix.SpecialLinearGroup.map (σ : F →+* F) M = N :=
      ⟨Matrix.SpecialLinearGroup.map (σ.symm : F →+* F) N, by
        apply Subtype.ext
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]⟩
    rw [← map_slConj]
    exact hcomm M
  have h2 : ∀ N : SL2 F,
      slConj (g⁻¹ * Matrix.GeneralLinearGroup.map (σ : F →+* F) g) N = N := by
    intro N
    rw [slConj_mul, h1, ← slConj_mul, inv_mul_cancel, slConj_one]
  obtain ⟨c, hc⟩ := eq_scalar_of_slConj_eq _ h2
  refine ⟨c, ?_⟩
  have e : (g : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ * Matrix.GeneralLinearGroup.map (σ : F →+* F) g : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
      ((Matrix.GeneralLinearGroup.map (σ : F →+* F) g : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel_left]
  calc (g : Matrix (Fin 2) (Fin 2) F).map σ
      = ((Matrix.GeneralLinearGroup.map (σ : F →+* F) g : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := rfl
    _ = (g : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ * Matrix.GeneralLinearGroup.map (σ : F →+* F) g : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := e.symm
    _ = (g : Matrix (Fin 2) (Fin 2) F) * (c • (1 : Matrix (Fin 2) (Fin 2) F)) := by rw [hc]
    _ = c • (g : Matrix (Fin 2) (Fin 2) F) := by rw [Matrix.mul_smul, Matrix.mul_one]

theorem exists_fixedGL_of_commute {F : Type} [Field F] [Finite F] (σ : F ≃+* F)
    (g : GL (Fin 2) F)
    (hcomm : ∀ M : SL2 F, Matrix.SpecialLinearGroup.map (σ : F →+* F) (slConj g M) =
      slConj g (Matrix.SpecialLinearGroup.map (σ : F →+* F) M))
    (hns : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) :
    ∃ g₀ : GL (Fin 2) (fixF σ),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g₀ : (fixF σ)ˣ) : fixF σ) ∧
      ∀ M : SL2 (fixF σ), slFixIncl σ (slConj g₀ M) = slConj g (slFixIncl σ M) := by
  obtain ⟨c, hc⟩ := exists_map_eq_smul_of_commute σ g hcomm
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  obtain ⟨ν, hν0, hν⟩ :=
    exists_fixed_smul_of_semilinear σ rfl (g : Matrix (Fin 2) (Fin 2) F) hdet c hc
  have hmem : ∀ i j, (ν • (g : Matrix (Fin 2) (Fin 2) F)) i j ∈ fixF σ := fun i j =>
    mem_fixF.2 (congrFun (congrFun hν i) j)
  let B : Matrix (Fin 2) (Fin 2) (fixF σ) :=
    Matrix.of fun i j => ⟨(ν • (g : Matrix (Fin 2) (Fin 2) F)) i j, hmem i j⟩
  have hBmap : B.map (fixF σ).subtype = ν • (g : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    rfl
  have hBdet : (fixF σ).subtype B.det = ν ^ 2 * (g : Matrix (Fin 2) (Fin 2) F).det := by
    rw [RingHom.map_det]
    have : (fixF σ).subtype.mapMatrix B = B.map (fixF σ).subtype := rfl
    rw [this, hBmap, Matrix.det_smul, Fintype.card_fin]
  have hBne : B.det ≠ 0 := by
    intro h
    have h' := hBdet
    rw [h, map_zero] at h'
    exact mul_ne_zero (pow_ne_zero 2 hν0) hdet h'.symm
  have hval : ((Matrix.GeneralLinearGroup.mkOfDetNeZero B hBne : GL (Fin 2) (fixF σ)) :
      Matrix (Fin 2) (Fin 2) (fixF σ)) = B := rfl
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B hBne, ?_, ?_⟩
  · rintro ⟨d, hd⟩
    apply hns
    rw [Matrix.GeneralLinearGroup.val_det_apply, hval] at hd
    refine ⟨(d : F) / ν, ?_⟩
    have h1 : ν ^ 2 * (g : Matrix (Fin 2) (Fin 2) F).det = (d : F) * (d : F) := by
      rw [← hBdet, hd]
      rfl
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    field_simp
    linear_combination h1
  · intro M
    have hGmat : ((Matrix.GeneralLinearGroup.map (fixF σ).subtype
        (Matrix.GeneralLinearGroup.mkOfDetNeZero B hBne) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = ν • (g : Matrix (Fin 2) (Fin 2) F) := hBmap
    have hscal : ((diagGL (Units.mk0 ν hν0) (Units.mk0 ν hν0) * g : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = ν • (g : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hG : Matrix.GeneralLinearGroup.map (fixF σ).subtype
        (Matrix.GeneralLinearGroup.mkOfDetNeZero B hBne) =
        diagGL (Units.mk0 ν hν0) (Units.mk0 ν hν0) * g := Units.ext (hGmat.trans hscal.symm)
    have key : ∀ M : SL2 (fixF σ),
        Matrix.SpecialLinearGroup.map (fixF σ).subtype
          (slConj (Matrix.GeneralLinearGroup.mkOfDetNeZero B hBne) M) =
        slConj g (Matrix.SpecialLinearGroup.map (fixF σ).subtype M) := by
      intro M
      rw [map_slConj, hG, slConj_mul, slConj_scalar]
    exact key M

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
