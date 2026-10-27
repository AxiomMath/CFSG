module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreAxis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] def NotRatProj (σ : F ≃+* F) (h : GL (Fin 3) F) : Prop :=
  ¬ ∃ c : F, c ≠ 0 ∧ ∀ i j, σ (c * (h : Matrix (Fin 3) (Fin 3) F) i j) =
    c * (h : Matrix (Fin 3) (Fin 3) F) i j

theorem joinH_mul_rat (h : GL (Fin 3) F) {k : GL (Fin 3) F} (hk : k ∈ ratGL σ) :
    joinH σ (h * k) = joinH σ h := by
  unfold joinH
  rw [conjGL3_mul, ← Subgroup.map_map, map_conjGL3_fixSL3 hk]

theorem conjGL3_scalar (u : Fˣ) : conjGL3 (Matrix.GeneralLinearGroup.scalar (Fin 3) u) =
    MonoidHom.id (SpecialLinearGroup (Fin 3) F) := by
  ext g i j
  rw [conjGL3_coe, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Matrix.mul_diagonal]
  simp only [MonoidHom.id_apply, Matrix.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val]
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero u), one_mul]

theorem joinH_scalar_mul (u : Fˣ) (h : GL (Fin 3) F) :
    joinH σ (Matrix.GeneralLinearGroup.scalar (Fin 3) u * h) = joinH σ h := by
  unfold joinH
  rw [conjGL3_mul, conjGL3_scalar, MonoidHom.id_comp]

theorem conjGL3_eq_of_mul_eq {h : GL (Fin 3) F} {x y : SpecialLinearGroup (Fin 3) F}
    (hxy : (h : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) =
      (y : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F)) : conjGL3 h x = y := by
  apply Subtype.ext
  rw [conjGL3_coe, hxy, Matrix.mul_assoc, coe_mul_inv, Matrix.mul_one]

@[expose] noncomputable def uniGL (β γ : F) : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, β, γ; 0, 1, 0; 0, 0, 1]
    (by simp [Matrix.det_fin_three])

theorem coe_uniGL (β γ : F) :
    (uniGL β γ : Matrix (Fin 3) (Fin 3) F) = !![1, β, γ; 0, 1, 0; 0, 0, 1] := rfl

theorem top_le_joinH_uni [Finite F] (hr : (orderOf σ).Prime) {β γ : F}
    (hnr : ¬ (σ β = β ∧ σ γ = γ)) : ⊤ ≤ joinH σ (uniGL β γ) := by
  have hA := fixSL3_le_joinH (σ := σ) (uniGL β γ)
  have hx12 : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F) ∈
      fixSL3 σ := transvection_mem_fixSL3 _ (map_one σ)
  have hx21 : SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : F) ∈
      fixSL3 σ := transvection_mem_fixSL3 _ (map_one σ)
  have e1 : conjGL3 (uniGL β γ)
      (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F)) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) β *
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F) := by
    apply conjGL3_eq_of_mul_eq
    simp only [coe_uniGL, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
    all_goals ring
  have e2 : conjGL3 (uniGL β γ)
      (SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : F)) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) γ *
        SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : F) := by
    apply conjGL3_eq_of_mul_eq
    simp only [coe_uniGL, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
  have m1 : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) β *
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F) ∈
        joinH σ (uniGL β γ) := by
    rw [← e1]
    exact Subgroup.mem_sup_right ⟨_, hx12, rfl⟩
  have m2 : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) γ *
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : F) ∈
        joinH σ (uniGL β γ) := by
    rw [← e2]
    exact Subgroup.mem_sup_right ⟨_, hx21, rfl⟩
  have m1' : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) β ∈
      joinH σ (uniGL β γ) := by
    have := (joinH σ (uniGL β γ)).mul_mem m1 ((joinH σ (uniGL β γ)).inv_mem (hA hx12))
    rwa [mul_inv_cancel_right] at this
  have m2' : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) γ ∈
      joinH σ (uniGL β γ) := by
    have := (joinH σ (uniGL β γ)).mul_mem m2 ((joinH σ (uniGL β γ)).inv_mem (hA hx21))
    rwa [mul_inv_cancel_right] at this
  by_cases hβ : σ β = β
  · exact top_le_of_x01 hA hr m2' (fun hγ => hnr ⟨hβ, hγ⟩)
  · exact top_le_of_x02 hA hr m1' hβ

theorem top_le_joinH_of_fix [Finite F] (hr : (orderOf σ).Prime) {h : GL (Fin 3) F}
    (he : (h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (hnr : NotRatProj σ h) : ⊤ ≤ joinH σ h := by
  have hA := fixSL3_le_joinH (σ := σ) h
  obtain ⟨hi, hhi⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F,
      M = ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
  have hie : hi *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    calc hi *ᵥ Pi.single 0 1 = hi *ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) := by
          rw [he]
      _ = Pi.single 0 1 := by rw [Matrix.mulVec_mulVec, hhi, coe_inv_mul, Matrix.one_mulVec]
  have hcol : ∀ i, hi i 0 = (Pi.single 0 (1 : F) : Fin 3 → F) i := fun i => by
    have := congrFun hie i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h00 : hi 0 0 = 1 := by rw [hcol]; rfl
  have h10 : hi 1 0 = 0 := by rw [hcol]; rfl
  have h20 : hi 2 0 = 0 := by rw [hcol]; rfl
  have hrat_e0 : IsRat σ (Pi.single 0 (1 : F) : Fin 3 → F) := fun j => by
    by_cases hj : j = 0 <;> simp [hj]
  have he0 : (Pi.single 0 (1 : F) : Fin 3 → F) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
  have hrow : ∀ i : Fin 3, i ≠ 0 →
      tv (Pi.single 0 1) (fun j => hi i j) ∈ joinH σ h := by
    intro i hi0
    have hd : (Pi.single i (1 : F) : Fin 3 → F) ⬝ᵥ Pi.single 0 1 = 0 := by
      simp [dotProduct, Pi.single_apply, Ne.symm hi0]
    have hrat2 : IsRat σ (Pi.single i (1 : F) : Fin 3 → F) := fun j => by
      by_cases hj : j = i <;> simp [hj]
    have hmem := conj_tv_mem_joinH h hd hrat_e0 hrat2
    rw [he, ← hhi] at hmem
    have hrw : (Pi.single i (1 : F) : Fin 3 → F) ᵥ* hi = fun j => hi i j := by
      funext j
      fin_cases i <;> simp [Matrix.vecMul, dotProduct, Pi.single_apply]
    rwa [hrw] at hmem
  have hrows : ∀ i : Fin 3, i ≠ 0 → IsRat σ (fun j => hi i j) ∨ ⊤ ≤ joinH σ h := by
    intro i hi0
    by_cases hri : IsRat σ (fun j => hi i j)
    · exact Or.inl hri
    · refine Or.inr (top_le_of_tv_rat_center hr hA hrat_e0 he0 ?_ hri (hrow i hi0))
      simp [dotProduct, Pi.single_apply, hcol, hi0]
  rcases hrows 1 (by decide) with hr1 | htop
  swap
  · exact htop
  rcases hrows 2 (by decide) with hr2 | htop
  swap
  · exact htop
  have hk : h⁻¹ * uniGL (-(hi 0 1)) (-(hi 0 2)) ∈ ratGL σ := by
    rw [mem_ratGL]
    intro i j
    have hkij : ((h⁻¹ * uniGL (-(hi 0 1)) (-(hi 0 2)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) i j =
        hi i 0 * !![1, -(hi 0 1), -(hi 0 2); 0, 1, 0; 0, 0, 1] 0 j +
          hi i 1 * !![1, -(hi 0 1), -(hi 0 2); 0, 1, 0; 0, 0, 1] 1 j +
            hi i 2 * !![1, -(hi 0 1), -(hi 0 2); 0, 1, 0; 0, 0, 1] 2 j := by
      rw [Units.val_mul, coe_uniGL, ← hhi, Matrix.mul_apply, Fin.sum_univ_three]
    rw [hkij]
    have r1 := fun j => hr1 j
    have r2 := fun j => hr2 j
    simp only at r1 r2
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, r1, r2]
  have hh : h = uniGL (-(hi 0 1)) (-(hi 0 2)) * (h⁻¹ * uniGL (-(hi 0 1)) (-(hi 0 2)))⁻¹ := by
    group
  rw [hh, joinH_mul_rat _ ((ratGL σ).inv_mem hk)]
  refine top_le_joinH_uni hr ?_
  rintro ⟨hβ, hγ⟩
  apply hnr
  refine ⟨1, one_ne_zero, ?_⟩
  simp only [one_mul]
  have hβ' : σ (hi 0 1) = hi 0 1 := by rw [map_neg] at hβ; exact neg_injective hβ
  have hγ' : σ (hi 0 2) = hi 0 2 := by rw [map_neg] at hγ; exact neg_injective hγ
  have hir : IsRatM σ ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← hhi]
    intro i j
    fin_cases i
    · fin_cases j
      · simp [h00]
      · exact hβ'
      · exact hγ'
    · exact hr1 j
    · exact hr2 j
  have := IsRatM.inv (g := h⁻¹) hir
  rwa [inv_inv] at this

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
