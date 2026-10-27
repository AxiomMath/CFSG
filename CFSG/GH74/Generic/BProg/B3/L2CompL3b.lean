module

public import CFSG.GH74.Generic.S45.LPsl3
public import CFSG.GH74.Generic.BProg.B3.L2CompSymD8

public section

namespace CFSG.GH74.Generic.BProg.B3.L2CompL3b

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Generic.S45
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification
open scoped MatrixGroups Matrix

@[expose] def IsD8 {G : Type*} [Group G] (a b : G) : Prop :=
  a ^ 4 = 1 ∧ a ^ 2 ≠ 1 ∧ b * b = 1 ∧ b * a * b⁻¹ = a⁻¹

theorem IsD8.map {G H : Type*} [Group G] [Group H] {a b : G} (h : IsD8 a b) (φ : G ≃* H) :
    IsD8 (φ a) (φ b) := by
  obtain ⟨h4, h2, hb, hba⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h4, map_one]
  · intro h
    apply h2
    apply φ.injective
    rw [map_pow, h, map_one]
  · rw [← map_mul, hb, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, hba, map_inv]

section B0

variable (F : Type*) [Field F]

@[expose] def b0SL : SL(3, F) := ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

variable {F}

@[simp] theorem b0SL_coe : ((b0SL F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0; 0, -1, 0; 0, 0, -1] := rfl

theorem b0SL_mul_self : b0SL F * b0SL F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, b0SL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem d0SL_comm_b0SL : d0SL F * b0SL F = b0SL F * d0SL F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, b0SL_coe, d0SL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem b0SL_g0SL_b0SL_g0SL : b0SL F * g0SL F * (b0SL F * g0SL F) = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, b0SL_coe,
    g0SL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem b0SL_conj_g0SL : b0SL F * g0SL F * (b0SL F)⁻¹ = (g0SL F)⁻¹ := by
  have h1 : (b0SL F)⁻¹ = b0SL F := inv_eq_of_mul_eq_one_right b0SL_mul_self
  have h2 : b0SL F * g0SL F * b0SL F = (g0SL F)⁻¹ := by
    have h3 : b0SL F * g0SL F * b0SL F * g0SL F = 1 := by
      simpa only [mul_assoc] using b0SL_g0SL_b0SL_g0SL (F := F)
    exact mul_eq_one_iff_eq_inv.1 h3
  rw [h1, h2]

theorem map_b0SL (σ : F ≃+* F) : Matrix.SpecialLinearGroup.map σ.toRingHom (b0SL F) = b0SL F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem graphAut_b0SL : (b0SL F)⁻¹.transpose = b0SL F := by
  have h : (b0SL F)⁻¹ = b0SL F := inv_eq_of_mul_eq_one_right b0SL_mul_self
  rw [h]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, b0SL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem isD8_proj_g0_b0 (h2 : (2 : F) ≠ 0) :
    IsD8 (LinearFlag.proj 3 F (g0SL F)) (LinearFlag.proj 3 F (b0SL F)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow, g0SL_pow_four, map_one]
  · exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [orderOf_proj_g0SL h2]; norm_num)
  · rw [← map_mul, b0SL_mul_self, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, b0SL_conj_g0SL, map_inv]

end B0

section Inner

theorem inner_conj_d0 {F : Type} [Field F] [Finite F] (hk2 : ringChar F ≠ 2)
    {B : Matrix.GeneralLinearGroup (Fin 3) F} (hB2 : LinearFlag.conjAut 3 F B ^ 2 = 1)
    (hB1 : LinearFlag.conjAut 3 F B ≠ 1) :
    ∃ g : SL(3, F), ∀ h : SL(3, F), LinearFlag.conjAut 3 F B (LinearFlag.proj 3 F h) =
      LinearFlag.proj 3 F ((g⁻¹ * d0SL F * g) * h * (g⁻¹ * d0SL F * g)⁻¹) := by
  classical
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hk2
  have hm3 : 3 ≤ 3 := le_refl 3
  have h2' : LinearFlag.conjAut 3 F (B ^ 2) = 1 := by rw [map_pow]; exact hB2
  obtain ⟨μ, hμ⟩ := (conjAut_eq_one_iff hm3 _).mp h2'
  have hBB : (B : Matrix (Fin 3) (Fin 3) F) * B = (μ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 3) F =>
      (A : Matrix (Fin 3) (Fin 3) F)) hμ
    simp only [pow_two, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [← this, Matrix.smul_one_eq_diagonal]
    rfl
  have hdet : ((B : Matrix (Fin 3) (Fin 3) F).det) * (B : Matrix (Fin 3) (Fin 3) F).det =
      (μ : F) ^ 3 := by
    have := congrArg Matrix.det hBB
    rwa [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
  have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
  set s : F := (B : Matrix (Fin 3) (Fin 3) F).det / (μ : F) with hs
  have hs0 : s ≠ 0 := by
    intro h
    have : (B : Matrix (Fin 3) (Fin 3) F).det = 0 := by
      rw [hs, div_eq_zero_iff] at h
      exact h.resolve_right hμ0
    exact (Matrix.isUnit_iff_isUnit_det _ |>.1 B.isUnit).ne_zero this
  have hss : s * s = μ := by
    rw [hs]
    field_simp
    linear_combination hdet
  have hdetB : (B : Matrix (Fin 3) (Fin 3) F).det = s * μ := by
    rw [hs]
    field_simp
  let Bm : Matrix (Fin 3) (Fin 3) F := s⁻¹ • (B : Matrix (Fin 3) (Fin 3) F)
  have hBm2 : Bm * Bm = 1 := by
    simp only [Bm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hBB]
    have : s⁻¹ * (s⁻¹ * μ) = 1 := by
      rw [← hss]
      field_simp
    rw [this, one_smul]
  have hBmdet : Bm.det = 1 := by
    simp only [Bm, Matrix.det_smul, Fintype.card_fin, hdetB]
    rw [← hss]
    field_simp
  let B'' : SL(3, F) := ⟨Bm, hBmdet⟩
  have hB''2 : B'' * B'' = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact hBm2)
  have hBc : (B : GL (Fin 3) F) = Matrix.SpecialLinearGroup.toGL B'' *
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 s hs0) := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    show (B : Matrix (Fin 3) (Fin 3) F) = Bm * Matrix.scalar (Fin 3) s
    simp only [Bm, Matrix.smul_mul, Matrix.scalar_apply]
    ext i j
    simp [Matrix.smul_apply]
    field_simp
  have hconj : LinearFlag.conjAut 3 F B =
      LinearFlag.conjAut 3 F (Matrix.SpecialLinearGroup.toGL B'') := by
    rw [(conjAut_eq_conjAut_iff hm3 _ _).2 ⟨Units.mk0 s hs0, hBc⟩]
  have hB''1 : B'' ≠ 1 := by
    intro h
    apply hB1
    rw [hconj, h, map_one, map_one]
  obtain ⟨g, hg⟩ := (CFSG.GH74.Generic.S3.singleInv_sl3 htwo) B'' (d0SL F) hB''2 hB''1
    d0SL_mul_self (d0SL_ne_one htwo)
  have hB''eq : B'' = g⁻¹ * d0SL F * g := by rw [← hg]; group
  have hsl : ∀ h : SL(3, F), CatalogueBHigherLinearAction.slConjugation 3 F
      (Matrix.SpecialLinearGroup.toGL B'') h = B'' * h * B''⁻¹ := by
    intro h
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CatalogueBHigherLinearAction.toGL_slConjugation]
    simp [map_mul, map_inv]
  refine ⟨g, fun h => ?_⟩
  rw [hconj, LinearFlag.conjAut_proj, hsl, hB''eq]

theorem psl_three_fixed_inner_D8 {F : Type} [Field F] [Finite F] (hk2 : ringChar F ≠ 2)
    {B : Matrix.GeneralLinearGroup (Fin 3) F} (hB2 : LinearFlag.conjAut 3 F B ^ 2 = 1)
    (hB1 : LinearFlag.conjAut 3 F B ≠ 1) :
    ∃ p q : LinearFlag.projectiveSL 3 F, LinearFlag.conjAut 3 F B p = p ∧
      LinearFlag.conjAut 3 F B q = q ∧ IsD8 p q := by
  obtain ⟨g, hg⟩ := inner_conj_d0 hk2 hB2 hB1
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hk2
  have hc : d0SL F * g0SL F * (d0SL F)⁻¹ = g0SL F := by
    rw [mul_inv_eq_iff_eq_mul]
    exact d0SL_comm_g0SL
  have hc' : d0SL F * b0SL F * (d0SL F)⁻¹ = b0SL F := by
    rw [mul_inv_eq_iff_eq_mul]
    exact d0SL_comm_b0SL
  refine ⟨LinearFlag.proj 3 F (g⁻¹ * g0SL F * g), LinearFlag.proj 3 F (g⁻¹ * b0SL F * g),
    ?_, ?_, ?_⟩
  · rw [hg]
    congr 1
    calc g⁻¹ * d0SL F * g * (g⁻¹ * g0SL F * g) * (g⁻¹ * d0SL F * g)⁻¹
        = g⁻¹ * (d0SL F * g0SL F * (d0SL F)⁻¹) * g := by group
      _ = g⁻¹ * g0SL F * g := by rw [hc]
  · rw [hg]
    congr 1
    calc g⁻¹ * d0SL F * g * (g⁻¹ * b0SL F * g) * (g⁻¹ * d0SL F * g)⁻¹
        = g⁻¹ * (d0SL F * b0SL F * (d0SL F)⁻¹) * g := by group
      _ = g⁻¹ * b0SL F * g := by rw [hc']
  · have h := (isD8_proj_g0_b0 htwo).map (MulAut.conj (LinearFlag.proj 3 F g)⁻¹)
    have e1 : ∀ x : SL(3, F), (MulAut.conj (LinearFlag.proj 3 F g)⁻¹) (LinearFlag.proj 3 F x) =
        LinearFlag.proj 3 F (g⁻¹ * x * g) := by
      intro x
      simp [map_mul, map_inv]
    rw [e1, e1] at h
    exact h

end Inner

section Graph

theorem fixed_of_isometry {F : Type} [Field F] {m : ℕ}
    (B : Matrix.GeneralLinearGroup (Fin m) F) (hB : (B : Matrix (Fin m) (Fin m) F)ᵀ = B)
    (c : Matrix.SpecialLinearGroup (Fin m) F)
    (hcB : (c : Matrix (Fin m) (Fin m) F) * B * (c : Matrix (Fin m) (Fin m) F)ᵀ = B) :
    (CatalogueBHigherLinearAction.slConjugation m F B * CatalogueBGraphForm.slGraphAut m F) c =
      c := by
  apply Subtype.ext
  change ((CatalogueBHigherLinearAction.slConjugation m F B
      (CatalogueBGraphForm.slGraphAut m F c) : Matrix.SpecialLinearGroup (Fin m) F) :
        Matrix (Fin m) (Fin m) F) = _
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, CatalogueBGraphForm.slGraphAut_matrix]
  set cm : Matrix (Fin m) (Fin m) F := (c : Matrix (Fin m) (Fin m) F) with hcm
  set c' : Matrix (Fin m) (Fin m) F :=
    ((c⁻¹ : Matrix.SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) with hc'
  have h1 : c' * cm = 1 := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin m) F =>
      (g : Matrix (Fin m) (Fin m) F)) (inv_mul_cancel c)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
    exact this
  have h2' : B.val * cmᵀ = c' * B.val := by
    calc B.val * cmᵀ = (c' * cm) * B.val * cmᵀ := by rw [h1, Matrix.one_mul]
      _ = c' * (cm * B.val * cmᵀ) := by simp only [Matrix.mul_assoc]
      _ = c' * B.val := by rw [hcB]
  have h3 : cm * B.val = B.val * c'ᵀ := by
    have := congrArg Matrix.transpose h2'
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hB] at this
    exact this
  calc B.val * c'ᵀ * (B⁻¹).val = cm * B.val * (B⁻¹).val := by rw [h3]
    _ = cm := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem exists_symmetric_graph_D8_proj {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (B : Matrix.GeneralLinearGroup (Fin 3) F) (hB : (B : Matrix (Fin 3) (Fin 3) F)ᵀ = B) :
    ∃ p q : LinearFlag.projectiveSL 3 F,
      (LinearFlag.conjAut 3 F B * LinearFlag.dualAut 3 F) p = p ∧
      (LinearFlag.conjAut 3 F B * LinearFlag.dualAut 3 F) q = q ∧ IsD8 p q := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hBdet : IsUnit (B : Matrix (Fin 3) (Fin 3) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  obtain ⟨cm, bm, hcdet, hcB, hnsc, hc4, hbdet, hbB, hb2, hbc⟩ :=
    L2CompSymD8.exists_isometry_D8 h2 (le_refl 3) (B : Matrix (Fin 3) (Fin 3) F) hB hBdet
  let c : Matrix.SpecialLinearGroup (Fin 3) F := ⟨cm, hcdet⟩
  let b : Matrix.SpecialLinearGroup (Fin 3) F := ⟨bm, hbdet⟩
  have hcc : (c : Matrix (Fin 3) (Fin 3) F) = cm := rfl
  have hbb : (b : Matrix (Fin 3) (Fin 3) F) = bm := rfl
  have hc4' : c ^ 4 = 1 := by
    apply Subtype.ext
    have : c ^ 4 = (c * c) * (c * c) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [this]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hcc]
    exact hc4
  have hb2' : b * b = 1 := Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hbb]
    exact hb2)
  have hbc' : b * c * b⁻¹ = c⁻¹ := by
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2'
    have h3 : b * c * b = c * c * c := Subtype.ext (by
      simp only [Matrix.SpecialLinearGroup.coe_mul, hcc, hbb]
      exact hbc)
    have hci : c⁻¹ = c * c * c := inv_eq_of_mul_eq_one_right (Subtype.ext (by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hcc]
      rw [← hc4]
      simp only [Matrix.mul_assoc]))
    rw [hbi, h3, hci]
  have hfix : ∀ x : Matrix.SpecialLinearGroup (Fin 3) F,
      (x : Matrix (Fin 3) (Fin 3) F) * B * (x : Matrix (Fin 3) (Fin 3) F)ᵀ = B →
        (LinearFlag.conjAut 3 F B * LinearFlag.dualAut 3 F) (LinearFlag.proj 3 F x) =
          LinearFlag.proj 3 F x := by
    intro x hx
    rw [← proj_slConjugation_slGraphAut, fixed_of_isometry B hB x hx]
  refine ⟨LinearFlag.proj 3 F c, LinearFlag.proj 3 F b, hfix c hcB, hfix b hbB, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hc4', map_one]
  · intro h
    rw [← map_pow, LinearFlag.proj_eq_one_iff] at h
    obtain ⟨l, -, hl⟩ := h
    apply hnsc (l : F)
    have : ((c ^ 2 : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        cm * cm := by
      rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, hcc]
    rw [← this, hl, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  · rw [← map_mul, hb2', map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, hbc', map_inv]

end Graph

end CFSG.GH74.Generic.BProg.B3.L2CompL3b
