module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjective

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter Matrix Projectivization

universe u

@[expose] def diagonalGL (K : Type u) [Field K] (s : Kˣ) :
    Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(s : K), 0; 0, 1] (by
    simp [Matrix.det_fin_two])

theorem diagonalGL_det (K : Type u) [Field K] (s : Kˣ) :
    Matrix.GeneralLinearGroup.det (diagonalGL K s) = s := by
  apply Units.ext
  simp [diagonalGL, Matrix.det_fin_two]

theorem coordinatePGLAction_diagonal (K : Type u) [Field K] (s : Kˣ) :
    coordinatePGLAction K (Matrix.ProjGenLinGroup.mk (diagonalGL K s)) = multiplier K s := by
  apply Equiv.ext
  intro x
  apply (coordinateEquiv K).injective
  rw [coordinatePGLAction_point]
  cases x with
  | none =>
    rw [coordinateEquiv_none, multiplier_none, coordinateEquiv_none,
      psl2ProjectiveInfinity, Projectivization.PGL.mk_smul_mk,
      Projectivization.mk_eq_mk_iff']
    refine ⟨(s : K), ?_⟩
    change (s : K) • (![1, 0] : Fin 2 → K) = (diagonalGL K s).val *ᵥ ![1, 0]
    ext i
    fin_cases i <;> simp [diagonalGL, Matrix.mulVec]
  | some x =>
    rw [coordinateEquiv_some, multiplier_some, coordinateEquiv_some,
      psl2AffinePoint, psl2AffinePoint, Projectivization.PGL.mk_smul_mk,
      Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    change (1 : K) • (![(s : K) * x, 1] : Fin 2 → K) = (diagonalGL K s).val *ᵥ ![x, 1]
    ext i
    fin_cases i <;> simp [diagonalGL, Matrix.mulVec]

theorem coordinateG_le_D (K : Type u) [Field K] : coordinateG K ≤ coordinateD K := by
  intro g hg
  exact Subgroup.subset_closure (Or.inl hg)

theorem coordinateD_le_range (K : Type u) [Field K] :
    coordinateD K ≤ (coordinatePGLAction K).range := by
  apply (Subgroup.closure_le (coordinatePGLAction K).range).mpr
  intro g hg
  rcases hg with hg | ⟨s, rfl⟩
  · rw [← coordinatePSLAction_range_eq_G] at hg
    obtain ⟨h, rfl⟩ := hg
    exact ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL h, coordinatePGLAction_toPGL K h⟩
  · exact ⟨Matrix.ProjGenLinGroup.mk (diagonalGL K s), coordinatePGLAction_diagonal K s⟩

theorem coordinatePGLAction_range_eq_D (K : Type u) [Field K] :
    (coordinatePGLAction K).range = coordinateD K := by
  apply le_antisymm _ (coordinateD_le_range K)
  rintro g ⟨h, rfl⟩
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective h
  let s : Kˣ := Matrix.GeneralLinearGroup.det A
  let B := (diagonalGL K s)⁻¹ * A
  have hB : Matrix.GeneralLinearGroup.det B = 1 := by
    simp [B, diagonalGL_det, s]
  have hBmem : B ∈ Matrix.SpecialLinearGroup.toGL.range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hB
  obtain ⟨C, hC⟩ := hBmem
  have hA : A = diagonalGL K s * Matrix.SpecialLinearGroup.toGL C := by
    rw [hC]
    dsimp [B]
    group
  rw [hA, map_mul, map_mul]
  apply (coordinateD K).mul_mem
  · rw [coordinatePGLAction_diagonal]
    exact Subgroup.subset_closure (Or.inr ⟨s, rfl⟩)
  · rw [← Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, coordinatePGLAction_toPGL]
    apply coordinateG_le_D K
    rw [← coordinatePSLAction_range_eq_G]
    exact ⟨_, rfl⟩

theorem coordinateGLAction_range_eq_D (K : Type u) [Field K] :
    ((coordinatePGLAction K).comp Matrix.ProjGenLinGroup.mk).range = coordinateD K := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective,
    Subgroup.map_top, coordinatePGLAction_range_eq_D]

theorem coordinatePGLAction_injective (K : Type u) [Field K] [Finite K] :
    Function.Injective (coordinatePGLAction K) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hfix (x : PSL2ProjectiveLine K) : g • x = x := by
    obtain ⟨y, rfl⟩ := (coordinateEquiv K).surjective x
    have h := congrArg (fun a : Equiv.Perm (Omega K) => coordinateEquiv K (a y)) hg
    simpa only [coordinatePGLAction_point, Equiv.Perm.one_apply] using h
  obtain ⟨a, _ha, hu⟩ := existsUnique_pgl2_normalizes_projective_triple K
    (1 : Equiv.Perm (PSL2ProjectiveLine K))
  exact (hu g ⟨hfix _, hfix _, hfix _⟩).trans (hu 1 (by simp)).symm

@[expose] def pglEquivCoordinateD (K : Type u) [Field K] [Finite K] :
    PGL2 K ≃* coordinateD K :=
  (MulEquiv.ofBijective (coordinatePGLAction K).rangeRestrict
    ⟨fun _ _ h => coordinatePGLAction_injective K (congrArg Subtype.val h),
      (coordinatePGLAction K).rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr (coordinatePGLAction_range_eq_D K))

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
