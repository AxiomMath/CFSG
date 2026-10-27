module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessA

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3
  CFSG.Quasithin.H13.F431.L3.P3

@[expose] def gammaJM (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem gammaJM_mul_self (F : Type) [Field F] : gammaJM F * gammaJM F = 1 := by
  simp only [gammaJM, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem gammaJM_transpose (F : Type) [Field F] : (gammaJM F).transpose = gammaJM F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gammaJM]

@[expose] def gammaJ (F : Type) [Field F] : Matrix.GeneralLinearGroup (Fin 3) F :=
  Units.mk (gammaJM F) (gammaJM F) (gammaJM_mul_self F) (gammaJM_mul_self F)

theorem gammaJ_mul_inverseTranspose (F : Type) [Field F] :
    gammaJ F * Matrix.GeneralLinearGroup.inverseTranspose (gammaJ F) = 1 := by
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose, Units.val_one]
  change gammaJM F * (gammaJM F).transpose = 1
  rw [gammaJM_transpose, gammaJM_mul_self]

@[expose] noncomputable def gammaSL (F : Type) [Field F] (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F (gammaJ F)
    (g⁻¹).transpose

theorem coe_gammaSL (F : Type) [Field F] (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    ((gammaSL F g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      gammaJM F * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose *
        gammaJM F := by
  rw [gammaSL, coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
  rfl

@[expose] noncomputable def gammaAut (F : Type) [Field F] : MulAut (projectiveSL 3 F) :=
  conjAut 3 F (gammaJ F) * dualAut 3 F

theorem gammaAut_proj (F : Type) [Field F] (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    gammaAut F (proj 3 F g) = proj 3 F (gammaSL F g) := by
  rw [gammaAut, MulAut.mul_apply, dualAut_proj, conjAut_proj]
  rfl

theorem gammaAut_mul_self (F : Type) [Field F] : gammaAut F * gammaAut F = 1 := by
  obtain ⟨-, -, -, -, hdc, -⟩ := standard_automorphism_transport (n := 3) (K := F)
  calc gammaAut F * gammaAut F
      = conjAut 3 F (gammaJ F) * (dualAut 3 F * conjAut 3 F (gammaJ F) * dualAut 3 F) := by
        rw [gammaAut]
        simp only [mul_assoc]
    _ = conjAut 3 F (gammaJ F * Matrix.GeneralLinearGroup.inverseTranspose (gammaJ F)) := by
        rw [hdc, map_mul]
    _ = 1 := by
        rw [gammaJ_mul_inverseTranspose, map_one]

theorem gammaAut_gammaAut (F : Type) [Field F] (x : projectiveSL 3 F) :
    gammaAut F (gammaAut F x) = x := by
  rw [← MulAut.mul_apply, gammaAut_mul_self, MulAut.one_apply]

@[expose] def uSL (F : Type) [Field F] (a b c : F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, a, c; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_uSL (F : Type) [Field F] (a b c : F) :
    ((uSL F a b c : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, a, c; 0, 1, b; 0, 0, 1] :=
  rfl

theorem uSL_inv (F : Type) [Field F] (a b c : F) :
    (uSL F a b c)⁻¹ = uSL F (-a) (-b) (a * b - c) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_uSL, coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem gammaSL_uSL (F : Type) [Field F] (a b c : F) :
    gammaSL F (uSL F a b c) = uSL F (-b) (-a) (a * b - c) := by
  apply Subtype.ext
  rw [coe_gammaSL, uSL_inv]
  simp only [coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaJM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem uElt_eq_proj_uSL (F : Type) [Field F] (a b c : F) :
    uElt a b c = proj 3 F (uSL F a b c) := by
  have h : uElt a b c = wP (c - a * b) * xP a * yP b := by
    rw [wP_xP_yP_eq_uElt, sub_add_cancel]
  rw [h]
  unfold wP xP yP
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_wxy, coe_uSL, sub_add_cancel]

theorem gammaAut_uElt (F : Type) [Field F] [CharP F 2] (a b c : F) :
    gammaAut F (uElt a b c) = uElt b a (a * b + c) := by
  rw [uElt_eq_proj_uSL F a b c, uElt_eq_proj_uSL F b a (a * b + c), gammaAut_proj, gammaSL_uSL]
  congr 1
  simp only [CharTwo.neg_eq, CharTwo.sub_eq_add]

theorem uElt_eq_xP (F : Type) [Field F] (a : F) : uElt a 0 0 = xP a := by
  simp [uElt, (yP_eq_one_iff (0 : F)).2 rfl, (wP_eq_one_iff (0 : F)).2 rfl]

theorem uElt_zero_yP (F : Type) [Field F] (b : F) : uElt 0 b 0 = yP b := by
  simp [uElt, (xP_eq_one_iff (0 : F)).2 rfl, (wP_eq_one_iff (0 : F)).2 rfl]

theorem uElt_zero_zero_wP (F : Type) [Field F] (c : F) : uElt 0 0 c = wP c := by
  simp [uElt, (xP_eq_one_iff (0 : F)).2 rfl, (yP_eq_one_iff (0 : F)).2 rfl]

theorem gammaAut_xP (F : Type) [Field F] [CharP F 2] (a : F) :
    gammaAut F (xP a) = yP a := by
  rw [← uElt_eq_xP F a, gammaAut_uElt, mul_zero, add_zero, uElt_zero_yP]

theorem gammaAut_yP (F : Type) [Field F] [CharP F 2] (b : F) :
    gammaAut F (yP b) = xP b := by
  rw [← uElt_zero_yP F b, gammaAut_uElt, zero_mul, add_zero, uElt_eq_xP]

theorem gammaAut_wP (F : Type) [Field F] [CharP F 2] (c : F) :
    gammaAut F (wP c) = wP c := by
  rw [← uElt_zero_zero_wP F c, gammaAut_uElt, zero_mul, zero_add]

theorem gammaAut_map_V1 (F : Type) [Field F] [CharP F 2] :
    (V1 : Subgroup (projectiveSL 3 F)).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) =
      V2 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, c, rfl⟩ := mem_V1.mp hx
    show gammaAut F (xP a * wP c) ∈ V2
    rw [map_mul, gammaAut_xP, gammaAut_wP]
    exact mem_V2.mpr ⟨a, c, rfl⟩
  · intro y hy
    obtain ⟨b, c, rfl⟩ := mem_V2.mp hy
    refine ⟨gammaAut F (yP b * wP c), ?_, gammaAut_gammaAut F _⟩
    show gammaAut F (yP b * wP c) ∈ V1
    rw [map_mul, gammaAut_yP, gammaAut_wP]
    exact mem_V1.mpr ⟨b, c, rfl⟩

theorem gammaAut_map_V2 (F : Type) [Field F] [CharP F 2] :
    (V2 : Subgroup (projectiveSL 3 F)).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) =
      V1 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, c, rfl⟩ := mem_V2.mp hx
    show gammaAut F (yP b * wP c) ∈ V1
    rw [map_mul, gammaAut_yP, gammaAut_wP]
    exact mem_V1.mpr ⟨b, c, rfl⟩
  · intro y hy
    obtain ⟨a, c, rfl⟩ := mem_V1.mp hy
    refine ⟨gammaAut F (xP a * wP c), ?_, gammaAut_gammaAut F _⟩
    show gammaAut F (xP a * wP c) ∈ V2
    rw [map_mul, gammaAut_xP, gammaAut_wP]
    exact mem_V2.mpr ⟨a, c, rfl⟩

theorem gammaAut_map_Ln (F : Type) [Field F] [CharP F 2] :
    (Ln F).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) = Pt F := by
  have hb : Function.Bijective (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) :=
    (gammaAut F).bijective
  rw [Ln, Subgroup.map_normalizer_eq_of_bijective _ hb, gammaAut_map_V2]

theorem gammaAut_map_Pt (F : Type) [Field F] [CharP F 2] :
    (Pt F).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) = Ln F := by
  have hb : Function.Bijective (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) :=
    (gammaAut F).bijective
  rw [Pt, Subgroup.map_normalizer_eq_of_bijective _ hb, gammaAut_map_V1]

theorem gammaAut_mem_U (F : Type) [Field F] [CharP F 2] {x : projectiveSL 3 F}
    (hx : x ∈ projUnitriangular 3 F) : gammaAut F x ∈ projUnitriangular 3 F := by
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hx
  rw [wP_xP_yP_eq_uElt, gammaAut_uElt]
  exact uElt_mem_U _ _ _

theorem gammaAut_map_U (F : Type) [Field F] [CharP F 2] :
    (projUnitriangular 3 F).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) =
      projUnitriangular 3 F := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact gammaAut_mem_U F hx
  · intro y hy
    exact ⟨gammaAut F y, gammaAut_mem_U F hy, gammaAut_gammaAut F y⟩

theorem gammaAut_map_B0 (F : Type) [Field F] [CharP F 2] :
    (Ln F ⊓ Pt F).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) = Ln F ⊓ Pt F := by
  have hi : Function.Injective (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) :=
    (gammaAut F).injective
  rw [Subgroup.map_inf_eq _ _ _ hi, gammaAut_map_Ln, gammaAut_map_Pt, inf_comm]

theorem gammaAut_mem_Ln_iff (F : Type) [Field F] [CharP F 2] {x : projectiveSL 3 F} :
    x ∈ Ln F ↔ gammaAut F x ∈ Pt F := by
  constructor
  · intro hx
    have h : gammaAut F x ∈ (Ln F).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rwa [gammaAut_map_Ln] at h
  · intro hx
    have h : gammaAut F (gammaAut F x) ∈
        (Pt F).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) :=
      Subgroup.mem_map.mpr ⟨gammaAut F x, hx, rfl⟩
    rw [gammaAut_map_Pt, gammaAut_gammaAut] at h
    exact h

theorem gammaAut_mem_Pt_iff (F : Type) [Field F] [CharP F 2] {x : projectiveSL 3 F} :
    x ∈ Pt F ↔ gammaAut F x ∈ Ln F := by
  constructor
  · intro hx
    have h : gammaAut F x ∈ (Pt F).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rwa [gammaAut_map_Pt] at h
  · intro hx
    have h : gammaAut F (gammaAut F x) ∈
        (Ln F).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) :=
      Subgroup.mem_map.mpr ⟨gammaAut F x, hx, rfl⟩
    rw [gammaAut_map_Ln, gammaAut_gammaAut] at h
    exact h

theorem gammaAut_mem_B0_iff (F : Type) [Field F] [CharP F 2] {x : projectiveSL 3 F} :
    x ∈ Ln F ⊓ Pt F ↔ gammaAut F x ∈ Ln F ⊓ Pt F := by
  constructor
  · intro hx
    have h : gammaAut F x ∈
        (Ln F ⊓ Pt F).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rwa [gammaAut_map_B0] at h
  · intro hx
    have h : gammaAut F (gammaAut F x) ∈
        (Ln F ⊓ Pt F).map (gammaAut F : projectiveSL 3 F →* projectiveSL 3 F) :=
      Subgroup.mem_map.mpr ⟨gammaAut F x, hx, rfl⟩
    rw [gammaAut_map_B0, gammaAut_gammaAut] at h
    exact h

theorem gammaAut_proj_dMat (F : Type) [Field F] (t₁ t₂ : Fˣ) :
    gammaAut F (proj 3 F (dMat t₁ t₂)) = proj 3 F (dMat (t₁ * t₂) t₂⁻¹) := by
  rw [gammaAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_gammaSL, dMat_inv]
  simp only [coe_dMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaJM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      Matrix.diagonal_apply] <;> ring

theorem gammaAut_mem_torus3 (F : Type) [Field F] {g : projectiveSL 3 F} (hg : g ∈ torus3 F) :
    gammaAut F g ∈ torus3 F := by
  obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hg
  rw [gammaAut_proj_dMat]
  exact dP_mem_torus3 _ _

@[expose] noncomputable def gammaTorus (F : Type) [Field F] (τ : ↥(torus3 F)) : ↥(torus3 F) :=
  ⟨gammaAut F (τ : projectiveSL 3 F), gammaAut_mem_torus3 F τ.2⟩

theorem gammaTorus_gammaTorus (F : Type) [Field F] (τ : ↥(torus3 F)) :
    gammaTorus F (gammaTorus F τ) = τ :=
  Subtype.ext (gammaAut_gammaAut F _)

@[expose] noncomputable def gammaB (F : Type) [Field F] [CharP F 2] (b : ↥(Ln F ⊓ Pt F)) :
    ↥(Ln F ⊓ Pt F) :=
  ⟨gammaAut F (b : projectiveSL 3 F), (gammaAut_mem_B0_iff F).mp b.2⟩

theorem gammaB_val (F : Type) [Field F] [CharP F 2] (b : ↥(Ln F ⊓ Pt F)) :
    ((gammaB F b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) = gammaAut F (b : projectiveSL 3 F) :=
  rfl

theorem gammaB_nuNFEquiv (F : Type) [Field F] [Finite F] [CharP F 2] (a b c : F)
    (τ : ↥(torus3 F)) :
    gammaB F (nuNFEquiv F (a, b, c, τ)) = nuNFEquiv F (b, a, a * b + c, gammaTorus F τ) := by
  apply Subtype.ext
  simp only [gammaB_val, nuNFEquiv_val, map_mul, gammaAut_uElt, gammaTorus]

theorem nuCoord_left_false (F : Type) [Field F] (κ : F) (x : F × F × F × ↥(torus3 F)) :
    nuCoord 1 1 κ 0 false x = (x.1, x.2.1, x.2.2.1 + κ * x.1 ^ 2, x.2.2.2) := by
  simp [nuCoord, nuFrob]

theorem nuCoord_right_false (F : Type) [Field F] (κ : F) (x : F × F × F × ↥(torus3 F)) :
    nuCoord 1 1 0 κ false x = (x.1, x.2.1, x.2.2.1 + κ * x.2.1 ^ 2, x.2.2.2) := by
  simp [nuCoord, nuFrob]

theorem gammaB_conj_nuMap (F : Type) [Field F] [Finite F] [CharP F 2] (κ : F)
    (b : ↥(Ln F ⊓ Pt F)) :
    gammaB F (nuMap 1 1 κ 0 false (gammaB F b)) = nuMap 1 1 0 κ false b := by
  obtain ⟨⟨a, b', c, τ⟩, rfl⟩ := (nuNFEquiv F).surjective b
  rw [gammaB_nuNFEquiv]
  simp only [nuMap_nuNFEquiv, nuCoord_left_false, nuCoord_right_false]
  rw [gammaB_nuNFEquiv, gammaTorus_gammaTorus]
  have hc : b' * a + (a * b' + c + κ * b' ^ 2) = c + κ * b' ^ 2 := by
    linear_combination (a * b') * (CharTwo.two_eq_zero : (2 : F) = 0)
  rw [hc]

end CFSG.GH74.QTGen4.DSGen4.L34
