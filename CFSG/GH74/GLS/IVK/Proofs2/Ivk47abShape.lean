module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.NoncommCoprod

public noncomputable section

open Matrix MatrixGroups

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

variable {F : Type} [Field F]


@[expose] noncomputable def cf (g : GL (Fin 2) F) (A : SL(2, F)) : SL(2, F) :=
  ⟨(g : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    rw [det_mul, det_mul, A.2, mul_one, ← det_mul, Units.mul_inv, det_one]⟩

theorem coe_cf (g : GL (Fin 2) F) (A : SL(2, F)) :
    ((cf g A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl

theorem cf_mul (g : GL (Fin 2) F) (A B : SL(2, F)) : cf g (A * B) = cf g A * cf g B := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_cf, coe_cf, coe_cf, Matrix.SpecialLinearGroup.coe_mul]
  calc (g : Matrix (Fin 2) (Fin 2) F) * ((A : Matrix (Fin 2) (Fin 2) F) * B) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = (g : Matrix (Fin 2) (Fin 2) F) * A * (((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (g : Matrix (Fin 2) (Fin 2) F)) * B * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
        rw [Units.inv_mul]; simp [Matrix.mul_assoc]
    _ = _ := by simp [Matrix.mul_assoc]

theorem cf_cf_inv (g : GL (Fin 2) F) (A : SL(2, F)) : cf g (cf g⁻¹ A) = A := by
  apply Subtype.ext
  rw [coe_cf, coe_cf]
  simp only [inv_inv]
  calc (g : Matrix (Fin 2) (Fin 2) F) * (((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * A * g) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = ((g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * A *
        ((g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
        simp [Matrix.mul_assoc]
    _ = A := by rw [Units.mul_inv]; simp

@[expose] noncomputable def conjSLAut (g : GL (Fin 2) F) : MulAut SL(2, F) where
  toFun := cf g
  invFun := cf g⁻¹
  left_inv A := by simpa using cf_cf_inv g⁻¹ A
  right_inv A := cf_cf_inv g A
  map_mul' := cf_mul g

theorem conjSLAut_coe (g : GL (Fin 2) F) (A : SL(2, F)) :
    ((conjSLAut g A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl


theorem conjSLAut_mul (g h : GL (Fin 2) F) (A : SL(2, F)) :
    conjSLAut (g * h) A = conjSLAut g (conjSLAut h A) := by
  apply Subtype.ext
  rw [conjSLAut_coe, conjSLAut_coe, conjSLAut_coe]
  simp only [_root_.mul_inv_rev, Units.val_mul]
  simp [Matrix.mul_assoc]

theorem scalar_of_commute_SL2 (M : Matrix (Fin 2) (Fin 2) F)
    (h : ∀ A : SL(2, F), M * (A : Matrix (Fin 2) (Fin 2) F) = (A : Matrix (Fin 2) (Fin 2) F) * M) :
    ∃ c : F, M = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := M) (fun t =>
    (h ⟨t.toMatrix, t.det⟩).symm)
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem mem_sup_of_commute {Y : Type} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let S : Subgroup Y :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h a' ha' b hb]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h1 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
          have := h a ha b hb
          calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
            _ = (a * b)⁻¹ := by rw [← this]
            _ = b⁻¹ * a⁻¹ := by group
        rw [h1]; group }
  have : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact this hx

@[expose] def compMat (δ : F) : Matrix (Fin 2) (Fin 2) F := !![0, -δ; 1, 0]

theorem exists_conj_companion {g : GL (Fin 2) F}
    (hsc : ∃ μ : F, (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = μ • 1)
    (hns : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) :
    ∃ c : GL (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) =
      (c : Matrix (Fin 2) (Fin 2) F) * compMat ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
  obtain ⟨μ, hμ⟩ := hsc
  set M : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = M.det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
  obtain ⟨δ, hδ⟩ : ∃ δ : F, δ = M.det := ⟨_, rfl⟩
  rw [hdet, ← hδ] at hns ⊢
  rw [Matrix.eta_fin_two M] at hμ ⊢
  set a := M 0 0 with ha
  set b := M 0 1 with hb
  set c := M 1 0 with hc
  set d := M 1 1 with hd
  have e00 := congrFun (congrFun hμ 0) 0
  have e01 := congrFun (congrFun hμ 0) 1
  have e10 := congrFun (congrFun hμ 1) 0
  have e11 := congrFun (congrFun hμ 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdetM : δ = a * d - b * c := by rw [hδ, Matrix.det_fin_two]
  have htr : a + d = 0 := by
    by_contra hne
    have hb0 : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hne
    have hc0 : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hne
    have had : a = d := by
      have h1 : (a - d) * (a + d) = 0 := by
        rw [hb0, hc0] at e00 e11
        linear_combination e00 - e11
      have := (mul_eq_zero.mp h1).resolve_right hne
      linear_combination this
    apply hns
    refine ⟨a, ?_⟩
    rw [hdetM, hb0, hc0, ← had]; ring
  have hd' : d = -a := by linear_combination htr
  have hμ' : μ = a ^ 2 + b * c := by linear_combination -e00
  have hδ' : δ = -(a ^ 2 + b * c) := by rw [hdetM, hd']; ring
  rw [hδ']
  by_cases hcne : c = 0
  · by_cases hbne : b = 0
    ·
      have had : a ≠ d := by
        intro had; apply hns; refine ⟨a, ?_⟩; rw [hdetM, hbne, hcne, ← had]; ring
      have h2a : (2 : F) * a ≠ 0 := by
        intro h; apply had; rw [hd']; linear_combination h
      let cm : Matrix (Fin 2) (Fin 2) F := !![1, a; 1, d]
      have hcm : cm.det ≠ 0 := by
        rw [Matrix.det_fin_two]
        simp only [cm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        intro h; apply h2a; rw [hd'] at h; linear_combination -h
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero cm hcm, ?_⟩
      show (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) * cm = cm * compMat (-(a ^ 2 + b * c))
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cm, compMat, Matrix.mul_apply, Fin.sum_univ_two, hbne, hcne, hd'] <;> ring
    ·
      let cm : Matrix (Fin 2) (Fin 2) F := !![0, b; 1, d]
      have hcm : cm.det ≠ 0 := by
        rw [Matrix.det_fin_two]
        simp only [cm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        intro h; apply hbne; linear_combination -h
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero cm hcm, ?_⟩
      show (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) * cm = cm * compMat (-(a ^ 2 + b * c))
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cm, compMat, Matrix.mul_apply, Fin.sum_univ_two, hcne, hd'] <;> ring
  · let cm : Matrix (Fin 2) (Fin 2) F := !![1, a; 0, c]
    have hcm : cm.det ≠ 0 := by
      rw [Matrix.det_fin_two]
      simp only [cm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      simpa using hcne
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero cm hcm, ?_⟩
    show (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) * cm = cm * compMat (-(a ^ 2 + b * c))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cm, compMat, Matrix.mul_apply, Fin.sum_univ_two, hd'] <;> ring


theorem exists_mul_sq_of_not_isSquare [Finite F] {a b : F} (ha : ¬IsSquare a) (hb : ¬IsSquare b) :
    ∃ u : F, u ≠ 0 ∧ b = u ^ 2 * a := by
  classical
  have := Fintype.ofFinite F
  have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ IsSquare.zero)
  have hχa : quadraticChar F a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have hχb : quadraticChar F b = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hb
  have hab : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have h1 : quadraticChar F (a * b) = 1 := by
    rw [map_mul, hχa, hχb]; norm_num
  obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare hab).mp h1
  have hr0 : r ≠ 0 := by
    intro h; apply hab; rw [hr, h]; ring
  refine ⟨r / a, div_ne_zero hr0 ha0, ?_⟩
  field_simp
  linear_combination hr


@[expose] def Adm (g : GL (Fin 2) F) : Prop :=
  (∃ μ : F, (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = μ • 1) ∧
    ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)

@[expose] noncomputable def compGL (δ : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (compMat (δ : F)) (by
    rw [compMat, Matrix.det_fin_two]; simp)

theorem coe_compGL (δ : Fˣ) : ((compGL δ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = compMat (δ : F) := rfl

@[expose] noncomputable def diagU (u : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (!![(u : F), 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) (by
    rw [Matrix.det_fin_two]; simp)

theorem coe_diagU (u : Fˣ) : ((diagU u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(u : F), 0; 0, 1] := rfl

theorem adm_eq_conj_comp {g : GL (Fin 2) F} (hg : Adm g) :
    ∃ c : GL (Fin 2) F, g = c * compGL (Matrix.GeneralLinearGroup.det g) * c⁻¹ := by
  obtain ⟨c, hc⟩ := exists_conj_companion hg.1 hg.2
  refine ⟨c, ?_⟩
  have : g * c = c * compGL (Matrix.GeneralLinearGroup.det g) := Units.ext hc
  calc g = (g * c) * c⁻¹ := by group
    _ = c * compGL (Matrix.GeneralLinearGroup.det g) * c⁻¹ := by rw [this]

theorem compGL_scale (u δ : Fˣ) :
    (compGL (u ^ 2 * δ) : GL (Fin 2) F) * diagU u =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagU u * compGL δ := by
  apply Units.ext
  simp only [Units.val_mul, coe_compGL, coe_diagU, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply, sq]

theorem exists_conj_scalar [Finite F] {g g' : GL (Fin 2) F} (hg : Adm g) (hg' : Adm g') :
    ∃ (E : GL (Fin 2) F) (u : Fˣ),
      g' = Matrix.GeneralLinearGroup.scalar (Fin 2) u * (E * g * E⁻¹) := by
  obtain ⟨c, hc⟩ := adm_eq_conj_comp hg
  obtain ⟨c', hc'⟩ := adm_eq_conj_comp hg'
  obtain ⟨w, hw0, hw⟩ := exists_mul_sq_of_not_isSquare hg.2 hg'.2
  set u : Fˣ := Units.mk0 w hw0 with hu
  have hδ : Matrix.GeneralLinearGroup.det g' = u ^ 2 * Matrix.GeneralLinearGroup.det g := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, hu, Units.val_mk0]
    exact hw
  set s : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) u with hs
  have hscentral : ∀ x : GL (Fin 2) F, x * s = s * x := fun x =>
    ((Subgroup.mem_center_iff.mp (by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩) x))
  have h1 : compGL (Matrix.GeneralLinearGroup.det g') =
      s * (diagU u * compGL (Matrix.GeneralLinearGroup.det g) * (diagU u)⁻¹) := by
    rw [hδ]
    have := compGL_scale (F := F) u (Matrix.GeneralLinearGroup.det g)
    rw [mul_assoc] at this
    calc compGL (u ^ 2 * Matrix.GeneralLinearGroup.det g)
        = (compGL (u ^ 2 * Matrix.GeneralLinearGroup.det g) * diagU u) * (diagU u)⁻¹ := by group
      _ = _ := by rw [compGL_scale, hs]; group
  have h2 : compGL (Matrix.GeneralLinearGroup.det g) = c⁻¹ * g * c := by
    calc compGL (Matrix.GeneralLinearGroup.det g)
        = c⁻¹ * (c * compGL (Matrix.GeneralLinearGroup.det g) * c⁻¹) * c := by group
      _ = c⁻¹ * g * c := by rw [← hc]
  refine ⟨c' * diagU u * c⁻¹, u, ?_⟩
  calc g' = c' * compGL (Matrix.GeneralLinearGroup.det g') * c'⁻¹ := hc'
    _ = c' * (s * (diagU u * (c⁻¹ * g * c) * (diagU u)⁻¹)) * c'⁻¹ := by rw [h1, h2]
    _ = s * (c' * (diagU u * (c⁻¹ * g * c) * (diagU u)⁻¹) * c'⁻¹) := by
        rw [← mul_assoc c' s, hscentral c']; group
    _ = s * (c' * diagU u * c⁻¹ * g * (c' * diagU u * c⁻¹)⁻¹) := by group

@[expose] def ConjData {Y : Type} [Group Y] (t : Y) (K : Subgroup Y) {F : Type} [Field F]
    (e : ↥K ≃* SL(2, F)) (g : GL (Fin 2) F) : Prop :=
  ∀ x : ↥K, ∃ y : ↥K, (y : Y) = t * (x : Y) * t⁻¹ ∧
    ((e y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * ((e x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)

theorem toGL_conjSLAut (g : GL (Fin 2) F) (X : SL(2, F)) :
    Matrix.SpecialLinearGroup.toGL (conjSLAut g X) = g * Matrix.SpecialLinearGroup.toGL X * g⁻¹ := by
  apply Units.ext
  simp [conjSLAut_coe, Units.val_mul]

theorem conjSLAut_toGL (A X : SL(2, F)) :
    conjSLAut (Matrix.SpecialLinearGroup.toGL A) X = A * X * A⁻¹ := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_conjSLAut]
  simp

theorem conjData_iff {Y : Type} [Group Y] {t : Y} {K : Subgroup Y} {e : ↥K ≃* SL(2, F)}
    {g : GL (Fin 2) F} :
    ConjData t K e g ↔ ∀ x : ↥K, ∃ y : ↥K, (y : Y) = t * (x : Y) * t⁻¹ ∧ e y = conjSLAut g (e x) := by
  constructor
  · intro h x
    obtain ⟨y, hy, hey⟩ := h x
    exact ⟨y, hy, Subtype.ext hey⟩
  · intro h x
    obtain ⟨y, hy, hey⟩ := h x
    exact ⟨y, hy, by rw [hey]; rfl⟩


section ConjDataFacts

variable {Y : Type} [Group Y] {t : Y} {K : Subgroup Y} {e : ↥K ≃* SL(2, F)} {g : GL (Fin 2) F}

theorem det_toGL (A : SL(2, F)) :
    ((Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL A) : Fˣ) : F) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.det_coe]

theorem isSquare_det_of_conjSLAut_eq (G : GL (Fin 2) F) (A : SL(2, F))
    (h : ∀ X : SL(2, F), conjSLAut G X = A * X * A⁻¹) :
    IsSquare ((Matrix.GeneralLinearGroup.det G : Fˣ) : F) := by
  set P : GL (Fin 2) F := (Matrix.SpecialLinearGroup.toGL A)⁻¹ * G with hP
  have hcomm : ∀ X : SL(2, F),
      (P : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) =
        (X : Matrix (Fin 2) (Fin 2) F) * (P : Matrix (Fin 2) (Fin 2) F) := by
    intro X
    have h1 := congrArg Matrix.SpecialLinearGroup.toGL (h X)
    rw [toGL_conjSLAut, map_mul, map_mul, map_inv] at h1
    have h2 : P * Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL X * P := by
      rw [hP]
      calc (Matrix.SpecialLinearGroup.toGL A)⁻¹ * G * Matrix.SpecialLinearGroup.toGL X
          = (Matrix.SpecialLinearGroup.toGL A)⁻¹ * (G * Matrix.SpecialLinearGroup.toGL X * G⁻¹) * G := by
            group
        _ = (Matrix.SpecialLinearGroup.toGL A)⁻¹ * (Matrix.SpecialLinearGroup.toGL A *
            Matrix.SpecialLinearGroup.toGL X * (Matrix.SpecialLinearGroup.toGL A)⁻¹) * G := by
            rw [h1]
        _ = _ := by group
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) h2
    simpa [Units.val_mul] using this
  obtain ⟨c, hc⟩ := scalar_of_commute_SL2 (P : Matrix (Fin 2) (Fin 2) F) hcomm
  have hG : G = Matrix.SpecialLinearGroup.toGL A * P := by rw [hP]; group
  have hdetG : ((Matrix.GeneralLinearGroup.det G : Fˣ) : F) = c * c := by
    rw [hG, map_mul, Units.val_mul, det_toGL, one_mul, Matrix.GeneralLinearGroup.val_det_apply, hc,
      Matrix.det_smul]
    simp [sq]
  exact ⟨c, hdetG⟩

theorem ConjData.conj_mem (h : ConjData t K e g) {x : Y} (hx : x ∈ K) : t * x * t⁻¹ ∈ K := by
  obtain ⟨y, hy, -⟩ := h ⟨x, hx⟩
  rw [← hy]; exact y.2

theorem ConjData.sq_scalar (h : ConjData t K e g) (ht : t * t = 1) :
    ∃ μ : F, (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = μ • 1 := by
  rw [conjData_iff] at h
  have hM : ∀ X : SL(2, F),
      ((g * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) =
        (X : Matrix (Fin 2) (Fin 2) F) * ((g * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro X
    obtain ⟨x, rfl⟩ := e.surjective X
    obtain ⟨y, hy, hey⟩ := h x
    obtain ⟨y', hy', hey'⟩ := h y
    have hxy : y' = x := by
      apply Subtype.ext
      rw [hy', hy]
      calc t * (t * (x : Y) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [ht]; group
    rw [hxy] at hey'
    have h3 : e x = conjSLAut g (conjSLAut g (e x)) := by rw [← hey, hey']
    have h4 := congrArg Matrix.SpecialLinearGroup.toGL h3
    rw [toGL_conjSLAut, toGL_conjSLAut] at h4
    have h5 : (g * g) * Matrix.SpecialLinearGroup.toGL (e x) =
        Matrix.SpecialLinearGroup.toGL (e x) * (g * g) := by
      calc (g * g) * Matrix.SpecialLinearGroup.toGL (e x)
          = (g * (g * Matrix.SpecialLinearGroup.toGL (e x) * g⁻¹) * g⁻¹) * (g * g) := by group
        _ = _ := by rw [← h4]
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) h5
    simpa [Units.val_mul] using this
  obtain ⟨c, hc⟩ := scalar_of_commute_SL2 _ hM
  exact ⟨c, by simpa [Units.val_mul] using hc⟩

end ConjDataFacts

section ConjDataFacts2

variable {Y : Type} [Group Y] {t : Y} {K : Subgroup Y} {e : ↥K ≃* SL(2, F)} {g : GL (Fin 2) F}

theorem ConjData.t_not_mem_sup {L : Subgroup Y} (h : ConjData t K e g)
    (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    (hns : ¬IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) : t ∉ K ⊔ L := by
  intro ht
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcomm ht
  apply hns
  refine isSquare_det_of_conjSLAut_eq g (e ⟨a, ha⟩) fun X => ?_
  obtain ⟨x, rfl⟩ := e.surjective X
  rw [conjData_iff] at h
  obtain ⟨y, hy, hey⟩ := h x
  have hy2 : y = ⟨a, ha⟩ * x * ⟨a, ha⟩⁻¹ := by
    apply Subtype.ext
    rw [hy, ← hab]
    have hbx : b * (x : Y) = (x : Y) * b := (hcomm x x.2 b hb).symm
    calc a * b * (x : Y) * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
      _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hbx]
      _ = ((⟨a, ha⟩ * x * ⟨a, ha⟩⁻¹ : ↥K) : Y) := by
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv]; group
  rw [← hey, hy2]
  simp [map_mul, map_inv]

theorem e_z_eq_neg_one {L : Subgroup Y} {z : Y} (hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    (hzK : z ∈ K) (hzL : z ∈ L) (hne : z ≠ 1) : e ⟨z, hzK⟩ = -1 := by
  have hc : e ⟨z, hzK⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro A
    obtain ⟨x, rfl⟩ := e.surjective A
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm x x.2 z hzL)
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hr2 : r * r = 1 := by simpa [sq] using hr
  have hr' : r = 1 ∨ r = -1 := mul_self_eq_one_iff.mp hr2
  rcases hr' with rfl | rfl
  · exfalso
    apply hne
    have : e ⟨z, hzK⟩ = 1 := by
      apply Subtype.ext
      rw [← hrz]; simp
    have := e.injective (this.trans (map_one e).symm)
    exact congrArg Subtype.val this
  · apply Subtype.ext
    rw [← hrz, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.scalar_apply]
    ext i j
    by_cases hij : i = j <;> simp [hij]

end ConjDataFacts2
theorem conjSLAut_of_scalar {g : GL (Fin 2) F} (μ : F)
    (hg : (g : Matrix (Fin 2) (Fin 2) F) = μ • (1 : Matrix (Fin 2) (Fin 2) F)) (A : SL(2, F)) :
    conjSLAut g A = A := by
  apply Subtype.ext
  rw [conjSLAut_coe]
  have hcomm : (g : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) := by
    rw [hg]; simp
  rw [hcomm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem conjSLAut_sq_eq {g : GL (Fin 2) F}
    (h : ∃ μ : F, (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = μ • 1)
    (A : SL(2, F)) : conjSLAut g (conjSLAut g A) = A := by
  obtain ⟨μ, hμ⟩ := h
  rw [← conjSLAut_mul]
  exact conjSLAut_of_scalar μ (by rw [Units.val_mul]; exact hμ) A



theorem mem_normalizer_of_commute {Y : Type} [Group Y] {H : Subgroup Y} {b : Y}
    (h : ∀ x ∈ H, b * x = x * b) : b ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have hc : b * (b * x * b⁻¹) = (b * x * b⁻¹) * b := h _ hx
    have : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * ((b * x * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hc]
        _ = b * x * b⁻¹ := by group
    rw [this]; exact hx

structure Shape (Y : Type) [Group Y] (F₁ F₂ : Type) [Field F₁] [Field F₂] where
  I₁ : Subgroup Y
  I₂ : Subgroup Y
  z : Y
  t : Y
  e₁ : ↥I₁ ≃* SL(2, F₁)
  e₂ : ↥I₂ ≃* SL(2, F₂)
  g₁ : GL (Fin 2) F₁
  g₂ : GL (Fin 2) F₂
  comm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a
  inter : I₁ ⊓ I₂ = Subgroup.zpowers z
  z_sq : z * z = 1
  z_ne : z ≠ 1
  gen : I₁ ⊔ I₂ ⊔ Subgroup.zpowers t = ⊤
  t_sq : t * t = 1
  ns₁ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g₁ : F₁ˣ) : F₁)
  ns₂ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g₂ : F₂ˣ) : F₂)
  act₁ : ConjData t I₁ e₁ g₁
  act₂ : ConjData t I₂ e₂ g₂

namespace Shape

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape Y F₁ F₂)

theorem z_mem₁ : S.z ∈ S.I₁ := by
  have : S.z ∈ S.I₁ ⊓ S.I₂ := by rw [S.inter]; exact Subgroup.mem_zpowers _
  exact this.1

theorem z_mem₂ : S.z ∈ S.I₂ := by
  have : S.z ∈ S.I₁ ⊓ S.I₂ := by rw [S.inter]; exact Subgroup.mem_zpowers _
  exact this.2

theorem e₁_z : S.e₁ ⟨S.z, S.z_mem₁⟩ = -1 :=
  e_z_eq_neg_one S.comm S.z_mem₁ S.z_mem₂ S.z_ne

theorem e₂_z : S.e₂ ⟨S.z, S.z_mem₂⟩ = -1 :=
  e_z_eq_neg_one (fun a ha b hb => (S.comm b hb a ha).symm) S.z_mem₂ S.z_mem₁ S.z_ne

theorem t_not_mem : S.t ∉ S.I₁ ⊔ S.I₂ :=
  S.act₁.t_not_mem_sup S.comm S.ns₁

theorem sq_scalar₁ : ∃ μ : F₁, (S.g₁ : Matrix (Fin 2) (Fin 2) F₁) * (S.g₁ : Matrix (Fin 2) (Fin 2) F₁) = μ • 1 :=
  S.act₁.sq_scalar S.t_sq

theorem sq_scalar₂ : ∃ μ : F₂, (S.g₂ : Matrix (Fin 2) (Fin 2) F₂) * (S.g₂ : Matrix (Fin 2) (Fin 2) F₂) = μ • 1 :=
  S.act₂.sq_scalar S.t_sq

theorem adm₁ : Adm S.g₁ := ⟨S.sq_scalar₁, S.ns₁⟩

theorem adm₂ : Adm S.g₂ := ⟨S.sq_scalar₂, S.ns₂⟩

theorem t_mem_normalizer₁ : S.t ∈ Subgroup.normalizer (S.I₁ : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => S.act₁.conj_mem hh
  · intro hh
    have := S.act₁.conj_mem hh
    have e : S.t * (S.t * h * S.t⁻¹) * S.t⁻¹ = h := by
      calc S.t * (S.t * h * S.t⁻¹) * S.t⁻¹ = (S.t * S.t) * h * (S.t * S.t)⁻¹ := by group
        _ = h := by rw [S.t_sq]; group
    rwa [e] at this

theorem t_mem_normalizer₂ : S.t ∈ Subgroup.normalizer (S.I₂ : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => S.act₂.conj_mem hh
  · intro hh
    have := S.act₂.conj_mem hh
    have e : S.t * (S.t * h * S.t⁻¹) * S.t⁻¹ = h := by
      calc S.t * (S.t * h * S.t⁻¹) * S.t⁻¹ = (S.t * S.t) * h * (S.t * S.t)⁻¹ := by group
        _ = h := by rw [S.t_sq]; group
    rwa [e] at this

theorem normal₁ : S.I₁.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← S.gen]
  refine sup_le (sup_le Subgroup.le_normalizer ?_) ?_
  · intro b hb
    exact mem_normalizer_of_commute fun x hx => (S.comm x hx b hb).symm
  · rw [Subgroup.zpowers_le]; exact S.t_mem_normalizer₁

theorem normal₂ : S.I₂.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← S.gen]
  refine sup_le (sup_le ?_ Subgroup.le_normalizer) ?_
  · intro a ha
    exact mem_normalizer_of_commute fun x hx => S.comm a ha x hx
  · rw [Subgroup.zpowers_le]; exact S.t_mem_normalizer₂

@[expose] def swap : Shape Y F₂ F₁ where
  I₁ := S.I₂
  I₂ := S.I₁
  z := S.z
  t := S.t
  e₁ := S.e₂
  e₂ := S.e₁
  g₁ := S.g₂
  g₂ := S.g₁
  comm a ha b hb := (S.comm b hb a ha).symm
  inter := by rw [inf_comm]; exact S.inter
  z_sq := S.z_sq
  z_ne := S.z_ne
  gen := by rw [sup_comm S.I₂ S.I₁]; exact S.gen
  t_sq := S.t_sq
  ns₁ := S.ns₂
  ns₂ := S.ns₁
  act₁ := S.act₂
  act₂ := S.act₁

end Shape

section Canonical

@[expose] def sgnHom {M : Type*} [Group M] (m : M) (hm : m * m = 1) : ℤˣ →* M where
  toFun u := if u = 1 then 1 else m
  map_one' := by simp
  map_mul' u v := by
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl <;> simp [hm, hne]

theorem sgnHom_neg_one {M : Type*} [Group M] (m : M) (hm : m * m = 1) : sgnHom m hm (-1) = m := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  simp [sgnHom, hne]

theorem sgnHom_one {M : Type*} [Group M] (m : M) (hm : m * m = 1) : sgnHom m hm 1 = 1 := by
  simp [sgnHom]

variable {F₁ F₂ : Type} [Field F₁] [Field F₂]

@[expose] noncomputable def alphaAut (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂) : MulAut (SL(2, F₁) × SL(2, F₂)) :=
  MulEquiv.prodCongr (conjSLAut g₁) (conjSLAut g₂)

theorem alphaAut_apply (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂) (A : SL(2, F₁)) (B : SL(2, F₂)) :
    alphaAut g₁ g₂ (A, B) = (conjSLAut g₁ A, conjSLAut g₂ B) := rfl

theorem alphaAut_sq (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂)
    (h₁ : ∃ μ : F₁, (g₁ : Matrix (Fin 2) (Fin 2) F₁) * (g₁ : Matrix (Fin 2) (Fin 2) F₁) = μ • 1)
    (h₂ : ∃ μ : F₂, (g₂ : Matrix (Fin 2) (Fin 2) F₂) * (g₂ : Matrix (Fin 2) (Fin 2) F₂) = μ • 1) :
    alphaAut g₁ g₂ * alphaAut g₁ g₂ = 1 := by
  apply MulEquiv.ext
  rintro ⟨A, B⟩
  show alphaAut g₁ g₂ (alphaAut g₁ g₂ (A, B)) = (A, B)
  rw [alphaAut_apply, alphaAut_apply, conjSLAut_sq_eq h₁, conjSLAut_sq_eq h₂]

@[expose] noncomputable def phi (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂)
    (h₁ : ∃ μ : F₁, (g₁ : Matrix (Fin 2) (Fin 2) F₁) * (g₁ : Matrix (Fin 2) (Fin 2) F₁) = μ • 1)
    (h₂ : ∃ μ : F₂, (g₂ : Matrix (Fin 2) (Fin 2) F₂) * (g₂ : Matrix (Fin 2) (Fin 2) F₂) = μ • 1) :
    ℤˣ →* MulAut (SL(2, F₁) × SL(2, F₂)) :=
  sgnHom (alphaAut g₁ g₂) (alphaAut_sq g₁ g₂ h₁ h₂)

abbrev Pgrp (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂)
    (h₁ : ∃ μ : F₁, (g₁ : Matrix (Fin 2) (Fin 2) F₁) * (g₁ : Matrix (Fin 2) (Fin 2) F₁) = μ • 1)
    (h₂ : ∃ μ : F₂, (g₂ : Matrix (Fin 2) (Fin 2) F₂) * (g₂ : Matrix (Fin 2) (Fin 2) F₂) = μ • 1) :
    Type :=
  (SL(2, F₁) × SL(2, F₂)) ⋊[phi g₁ g₂ h₁ h₂] ℤˣ

end Canonical

section Psi

variable {F₁ F₂ : Type} [Field F₁] [Field F₂] {Y : Type} [Group Y]

namespace Shape

variable (S : Shape Y F₁ F₂)

@[expose] noncomputable def fnHom : SL(2, F₁) × SL(2, F₂) →* Y :=
  (S.I₁.subtype.comp S.e₁.symm.toMonoidHom).noncommCoprod
    (S.I₂.subtype.comp S.e₂.symm.toMonoidHom)
    (fun A B => S.comm _ (S.e₁.symm A).2 _ (S.e₂.symm B).2)

theorem fnHom_apply (A : SL(2, F₁)) (B : SL(2, F₂)) :
    S.fnHom (A, B) = ((S.e₁.symm A : ↥S.I₁) : Y) * ((S.e₂.symm B : ↥S.I₂) : Y) := rfl

theorem fnHom_alpha (A : SL(2, F₁)) (B : SL(2, F₂)) :
    S.fnHom (alphaAut S.g₁ S.g₂ (A, B)) = S.t * S.fnHom (A, B) * S.t⁻¹ := by
  obtain ⟨y₁, hy₁, hey₁⟩ := conjData_iff.mp S.act₁ (S.e₁.symm A)
  obtain ⟨y₂, hy₂, hey₂⟩ := conjData_iff.mp S.act₂ (S.e₂.symm B)
  rw [MulEquiv.apply_symm_apply] at hey₁ hey₂
  have h1 : S.e₁.symm (conjSLAut S.g₁ A) = y₁ := by rw [← hey₁]; simp
  have h2 : S.e₂.symm (conjSLAut S.g₂ B) = y₂ := by rw [← hey₂]; simp
  rw [alphaAut_apply, fnHom_apply, fnHom_apply, h1, h2, hy₁, hy₂]
  group

@[expose] noncomputable def psi (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂)
    (h₁ : ∃ μ : F₁, (g₁ : Matrix (Fin 2) (Fin 2) F₁) * (g₁ : Matrix (Fin 2) (Fin 2) F₁) = μ • 1)
    (h₂ : ∃ μ : F₂, (g₂ : Matrix (Fin 2) (Fin 2) F₂) * (g₂ : Matrix (Fin 2) (Fin 2) F₂) = μ • 1)
    (hg₁ : S.g₁ = g₁) (hg₂ : S.g₂ = g₂) : Pgrp g₁ g₂ h₁ h₂ →* Y :=
  SemidirectProduct.lift S.fnHom (sgnHom S.t S.t_sq) (by
    subst hg₁ hg₂
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · ext ⟨A, B⟩
      simp [phi, sgnHom_one]
    · ext ⟨A, B⟩
      simp [phi, sgnHom_neg_one, S.fnHom_alpha])

theorem psi_apply (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂) (h₁ h₂) (hg₁ : S.g₁ = g₁)
    (hg₂ : S.g₂ = g₂) (x : Pgrp g₁ g₂ h₁ h₂) :
    S.psi g₁ g₂ h₁ h₂ hg₁ hg₂ x = S.fnHom x.left * sgnHom S.t S.t_sq x.right := rfl

end Shape

end Psi

section Kernel

variable {F₁ F₂ : Type} [Field F₁] [Field F₂] {Y : Type} [Group Y]

theorem mem_zpowers_of_sq {z : Y} (hz : z * z = 1) {a : Y} (ha : a ∈ Subgroup.zpowers z) :
    a = 1 ∨ a = z := by
  obtain ⟨k, rfl⟩ := ha
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hz
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; show z ^ (2 * m) = 1; rw [_root_.zpow_mul]; simp [hz2]
  · right; show z ^ (2 * m + 1) = z; rw [_root_.zpow_add, _root_.zpow_mul]; simp [hz2]

@[expose] noncomputable def kappa (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂)
    (h₁ : ∃ μ : F₁, (g₁ : Matrix (Fin 2) (Fin 2) F₁) * (g₁ : Matrix (Fin 2) (Fin 2) F₁) = μ • 1)
    (h₂ : ∃ μ : F₂, (g₂ : Matrix (Fin 2) (Fin 2) F₂) * (g₂ : Matrix (Fin 2) (Fin 2) F₂) = μ • 1) :
    Pgrp g₁ g₂ h₁ h₂ :=
  SemidirectProduct.inl ((-1 : SL(2, F₁)), (-1 : SL(2, F₂)))

namespace Shape

variable (S : Shape Y F₁ F₂) (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂)
    (h₁ : ∃ μ : F₁, (g₁ : Matrix (Fin 2) (Fin 2) F₁) * (g₁ : Matrix (Fin 2) (Fin 2) F₁) = μ • 1)
    (h₂ : ∃ μ : F₂, (g₂ : Matrix (Fin 2) (Fin 2) F₂) * (g₂ : Matrix (Fin 2) (Fin 2) F₂) = μ • 1)
    (hg₁ : S.g₁ = g₁) (hg₂ : S.g₂ = g₂)

theorem psi_surjective : Function.Surjective (S.psi g₁ g₂ h₁ h₂ hg₁ hg₂) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← S.gen]
  refine sup_le (sup_le ?_ ?_) ?_
  · intro a ha
    refine ⟨⟨(S.e₁ ⟨a, ha⟩, 1), 1⟩, ?_⟩
    rw [psi_apply, sgnHom_one, mul_one, fnHom_apply]
    simp
  · intro b hb
    refine ⟨⟨(1, S.e₂ ⟨b, hb⟩), 1⟩, ?_⟩
    rw [psi_apply, sgnHom_one, mul_one, fnHom_apply]
    simp
  · rw [Subgroup.zpowers_le]
    refine ⟨⟨(1, 1), -1⟩, ?_⟩
    rw [psi_apply, sgnHom_neg_one, fnHom_apply]
    simp

theorem symm_neg_one₁ : S.e₁.symm (-1) = ⟨S.z, S.z_mem₁⟩ := by
  rw [← S.e₁_z]; simp

theorem symm_neg_one₂ : S.e₂.symm (-1) = ⟨S.z, S.z_mem₂⟩ := by
  rw [← S.e₂_z]; simp

theorem ker_psi : (S.psi g₁ g₂ h₁ h₂ hg₁ hg₂).ker = Subgroup.zpowers (kappa g₁ g₂ h₁ h₂) := by
  apply le_antisymm
  · rintro ⟨⟨A, B⟩, u⟩ hp
    rw [MonoidHom.mem_ker, psi_apply] at hp
    rcases Int.units_eq_one_or u with rfl | rfl
    · rw [sgnHom_one, mul_one, fnHom_apply] at hp
      have hab : ((S.e₁.symm A : ↥S.I₁) : Y) = (((S.e₂.symm B : ↥S.I₂) : Y))⁻¹ :=
        eq_inv_of_mul_eq_one_left hp
      have hmem : ((S.e₁.symm A : ↥S.I₁) : Y) ∈ Subgroup.zpowers S.z := by
        rw [← S.inter]
        refine ⟨(S.e₁.symm A).2, ?_⟩
        rw [hab]; exact S.I₂.inv_mem (S.e₂.symm B).2
      rcases mem_zpowers_of_sq S.z_sq hmem with h0 | h0
      · have hA : A = 1 := by
          have h1 : S.e₁.symm A = 1 := Subtype.ext h0
          have := congrArg S.e₁ h1
          simpa using this
        have hb0 : ((S.e₂.symm B : ↥S.I₂) : Y) = 1 := by
          rw [h0, one_mul] at hp; exact hp
        have hB : B = 1 := by
          have h1 : S.e₂.symm B = 1 := Subtype.ext hb0
          have := congrArg S.e₂ h1
          simpa using this
        have : (⟨(A, B), 1⟩ : Pgrp g₁ g₂ h₁ h₂) = 1 := by rw [hA, hB]; rfl
        rw [this]; exact Subgroup.one_mem _
      · have hA : A = -1 := by
          have h1 : S.e₁.symm A = ⟨S.z, S.z_mem₁⟩ := Subtype.ext h0
          have := congrArg S.e₁ h1
          rw [MulEquiv.apply_symm_apply, S.e₁_z] at this
          exact this
        have hb0 : ((S.e₂.symm B : ↥S.I₂) : Y) = S.z := by
          rw [h0] at hp
          exact (eq_inv_of_mul_eq_one_right hp).trans (inv_eq_of_mul_eq_one_right S.z_sq)
        have hB : B = -1 := by
          have h1 : S.e₂.symm B = ⟨S.z, S.z_mem₂⟩ := Subtype.ext hb0
          have := congrArg S.e₂ h1
          rw [MulEquiv.apply_symm_apply, S.e₂_z] at this
          exact this
        have : (⟨(A, B), 1⟩ : Pgrp g₁ g₂ h₁ h₂) = kappa g₁ g₂ h₁ h₂ := by
          rw [hA, hB]; rfl
        rw [this]; exact Subgroup.mem_zpowers _
    · exfalso
      rw [sgnHom_neg_one, fnHom_apply] at hp
      apply S.t_not_mem
      have : S.t = (((S.e₁.symm A : ↥S.I₁) : Y) * ((S.e₂.symm B : ↥S.I₂) : Y))⁻¹ :=
        eq_inv_of_mul_eq_one_right hp
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (S.e₁.symm A).2)
        (Subgroup.mem_sup_right (S.e₂.symm B).2))
  · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, psi_apply]
    show S.fnHom ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) * sgnHom S.t S.t_sq 1 = 1
    rw [sgnHom_one, mul_one, fnHom_apply, S.symm_neg_one₁, S.symm_neg_one₂]
    exact S.z_sq

end Shape

end Kernel

section Uniqueness

variable {F₁ F₂ : Type} [Field F₁] [Field F₂] {Y Y' : Type} [Group Y] [Group Y']

theorem conjSLAut_scalar (u : Fˣ) (A : SL(2, F)) :
    conjSLAut (Matrix.GeneralLinearGroup.scalar (Fin 2) u) A = A :=
  conjSLAut_of_scalar (u : F) (by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]) A

theorem det_scalar_mul_conj (u : Fˣ) (E g : GL (Fin 2) F) :
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) u * (E * g * E⁻¹)) :
      Fˣ) : F) = (u : F) ^ 2 * ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
  rw [map_mul, map_mul, map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Fintype.card_fin]
  have : ((Matrix.GeneralLinearGroup.det E : Fˣ) : F) *
      (((Matrix.GeneralLinearGroup.det E : Fˣ)⁻¹ : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (u : F) ^ 2 * (((Matrix.GeneralLinearGroup.det E : Fˣ) : F) *
        ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) *
        (((Matrix.GeneralLinearGroup.det E : Fˣ)⁻¹ : Fˣ) : F))
      = (u : F) ^ 2 * ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) *
        (((Matrix.GeneralLinearGroup.det E : Fˣ) : F) *
        (((Matrix.GeneralLinearGroup.det E : Fˣ)⁻¹ : Fˣ) : F)) := by ring
    _ = _ := by rw [this]; ring

namespace Shape

@[expose] noncomputable def recoord₁ (S : Shape Y F₁ F₂) (E g' : GL (Fin 2) F₁) (u : F₁ˣ)
    (hg' : g' = Matrix.GeneralLinearGroup.scalar (Fin 2) u * (E * S.g₁ * E⁻¹)) :
    Shape Y F₁ F₂ where
  I₁ := S.I₁
  I₂ := S.I₂
  z := S.z
  t := S.t
  e₁ := S.e₁.trans (conjSLAut E)
  e₂ := S.e₂
  g₁ := g'
  g₂ := S.g₂
  comm := S.comm
  inter := S.inter
  z_sq := S.z_sq
  z_ne := S.z_ne
  gen := S.gen
  t_sq := S.t_sq
  ns₁ := by
    rw [hg', det_scalar_mul_conj]
    rintro ⟨r, hr⟩
    apply S.ns₁
    have hu : (u : F₁) ≠ 0 := u.ne_zero
    refine ⟨r / u, ?_⟩
    field_simp
    linear_combination hr
  ns₂ := S.ns₂
  act₁ := by
    rw [conjData_iff]
    intro x
    obtain ⟨y, hy, hey⟩ := conjData_iff.mp S.act₁ x
    refine ⟨y, hy, ?_⟩
    show conjSLAut E (S.e₁ y) = conjSLAut g' (conjSLAut E (S.e₁ x))
    rw [hey, hg', conjSLAut_mul, conjSLAut_scalar, ← conjSLAut_mul, ← conjSLAut_mul]
    congr 1
    group
  act₂ := S.act₂

end Shape

end Uniqueness

section Transport

@[expose] noncomputable def slMap {F F' : Type} [Field F] [Field F'] (σ : F ≃+* F') : SL(2, F) ≃* SL(2, F') where
  toFun := Matrix.SpecialLinearGroup.map σ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map σ.symm.toRingHom
  left_inv A := by apply Subtype.ext; ext i j; simp
  right_inv A := by apply Subtype.ext; ext i j; simp
  map_mul' := map_mul _

theorem slMap_coe {F F' : Type} [Field F] [Field F'] (σ : F ≃+* F') (A : SL(2, F)) :
    ((slMap σ A : SL(2, F')) : Matrix (Fin 2) (Fin 2) F') =
      (A : Matrix (Fin 2) (Fin 2) F).map σ := rfl

variable {F₁ F₂ F₁' : Type} [Field F₁] [Field F₂] [Field F₁'] {Y Y' : Type} [Group Y] [Group Y']

namespace Shape

@[expose] noncomputable def mapField₁ (S : Shape Y F₁ F₂) (σ : F₁ ≃+* F₁') : Shape Y F₁' F₂ where
  I₁ := S.I₁
  I₂ := S.I₂
  z := S.z
  t := S.t
  e₁ := S.e₁.trans (slMap σ)
  e₂ := S.e₂
  g₁ := Matrix.GeneralLinearGroup.map σ.toRingHom S.g₁
  g₂ := S.g₂
  comm := S.comm
  inter := S.inter
  z_sq := S.z_sq
  z_ne := S.z_ne
  gen := S.gen
  t_sq := S.t_sq
  ns₁ := by
    rintro ⟨r, hr⟩
    apply S.ns₁
    have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map σ.toRingHom S.g₁) :
        F₁'ˣ) : F₁') = σ ((Matrix.GeneralLinearGroup.det S.g₁ : F₁ˣ) : F₁) := by
      rw [Matrix.GeneralLinearGroup.map_det]; rfl
    rw [h1] at hr
    refine ⟨σ.symm r, ?_⟩
    apply σ.injective
    rw [hr]; simp
  ns₂ := S.ns₂
  act₁ := by
    intro x
    obtain ⟨y, hy, hey⟩ := S.act₁ x
    refine ⟨y, hy, ?_⟩
    have hinv : (((Matrix.GeneralLinearGroup.map σ.toRingHom S.g₁)⁻¹ : GL (Fin 2) F₁') :
        Matrix (Fin 2) (Fin 2) F₁') =
        ((S.g₁⁻¹ : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁).map σ := by
      rw [← Matrix.GeneralLinearGroup.map_inv]; rfl
    show (S.e₁ y : SL(2, F₁)).1.map σ =
      (S.g₁ : Matrix (Fin 2) (Fin 2) F₁).map σ * (S.e₁ x : SL(2, F₁)).1.map σ *
        (((Matrix.GeneralLinearGroup.map σ.toRingHom S.g₁)⁻¹ : GL (Fin 2) F₁') :
          Matrix (Fin 2) (Fin 2) F₁')
    rw [hinv]
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F₁ => M.map σ) hey
    simp only [Matrix.map_mul] at this
    exact this
  act₂ := S.act₂

end Shape

end Transport

namespace Shape

variable {F₁ F₂ : Type} [Field F₁] [Field F₂] {Y Y' : Type} [Group Y] [Group Y']

@[expose] noncomputable def mapEquiv (S : Shape Y F₁ F₂) (φ : Y ≃* Y') : Shape Y' F₁ F₂ where
  I₁ := S.I₁.map φ.toMonoidHom
  I₂ := S.I₂.map φ.toMonoidHom
  z := φ S.z
  t := φ S.t
  e₁ := (φ.subgroupMap S.I₁).symm.trans S.e₁
  e₂ := (φ.subgroupMap S.I₂).symm.trans S.e₂
  g₁ := S.g₁
  g₂ := S.g₂
  comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, S.comm a ha b hb]
  inter := by
    rw [← Subgroup.map_inf _ _ φ.toMonoidHom φ.injective, S.inter, MonoidHom.map_zpowers]
    rfl
  z_sq := by rw [← map_mul, S.z_sq, map_one]
  z_ne := fun h => S.z_ne (φ.injective (by rw [h, map_one]))
  gen := by
    have hz : Subgroup.zpowers (φ S.t) = (Subgroup.zpowers S.t).map φ.toMonoidHom :=
      (MonoidHom.map_zpowers φ.toMonoidHom S.t).symm
    rw [← Subgroup.map_sup, hz, ← Subgroup.map_sup, S.gen]
    exact Subgroup.map_top_of_surjective _ φ.surjective
  t_sq := by rw [← map_mul, S.t_sq, map_one]
  ns₁ := S.ns₁
  ns₂ := S.ns₂
  act₁ := by
    intro x'
    obtain ⟨y, hy, hey⟩ := S.act₁ ((φ.subgroupMap S.I₁).symm x')
    refine ⟨φ.subgroupMap S.I₁ y, ?_, ?_⟩
    · show φ (y : Y) = φ S.t * (x' : Y') * (φ S.t)⁻¹
      have hx' : (x' : Y') = φ (((φ.subgroupMap S.I₁).symm x' : ↥S.I₁) : Y) := by
        have := (φ.subgroupMap S.I₁).apply_symm_apply x'
        exact (congrArg Subtype.val this).symm
      rw [hx', hy, map_mul, map_mul, map_inv]
    · show ((S.e₁ ((φ.subgroupMap S.I₁).symm ((φ.subgroupMap S.I₁) y)) : SL(2, F₁)) :
          Matrix (Fin 2) (Fin 2) F₁) =
        (S.g₁ : Matrix (Fin 2) (Fin 2) F₁) *
          ((S.e₁ ((φ.subgroupMap S.I₁).symm x') : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) *
          ((S.g₁⁻¹ : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁)
      rw [MulEquiv.symm_apply_apply]; exact hey
  act₂ := by
    intro x'
    obtain ⟨y, hy, hey⟩ := S.act₂ ((φ.subgroupMap S.I₂).symm x')
    refine ⟨φ.subgroupMap S.I₂ y, ?_, ?_⟩
    · show φ (y : Y) = φ S.t * (x' : Y') * (φ S.t)⁻¹
      have hx' : (x' : Y') = φ (((φ.subgroupMap S.I₂).symm x' : ↥S.I₂) : Y) := by
        have := (φ.subgroupMap S.I₂).apply_symm_apply x'
        exact (congrArg Subtype.val this).symm
      rw [hx', hy, map_mul, map_mul, map_inv]
    · show ((S.e₂ ((φ.subgroupMap S.I₂).symm ((φ.subgroupMap S.I₂) y)) : SL(2, F₂)) :
          Matrix (Fin 2) (Fin 2) F₂) =
        (S.g₂ : Matrix (Fin 2) (Fin 2) F₂) *
          ((S.e₂ ((φ.subgroupMap S.I₂).symm x') : SL(2, F₂)) : Matrix (Fin 2) (Fin 2) F₂) *
          ((S.g₂⁻¹ : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂)
      rw [MulEquiv.symm_apply_apply]; exact hey

end Shape

namespace Shape

variable {F₁ F₂ F₁' F₂' : Type} [Field F₁] [Field F₂] [Field F₁'] [Field F₂'] {Y Y' : Type}
  [Group Y] [Group Y']

theorem mulEquiv_of_eq_g (S : Shape Y F₁ F₂) (S' : Shape Y' F₁ F₂) (h₁ : S.g₁ = S'.g₁)
    (h₂ : S.g₂ = S'.g₂) : Nonempty (Y ≃* Y') := by
  have hk := S.ker_psi S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ rfl rfl
  have hk' := S'.ker_psi S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ h₁.symm h₂.symm
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _
      (S.psi_surjective S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ rfl rfl)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hk.trans hk'.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (S'.psi_surjective S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ h₁.symm h₂.symm)))⟩

theorem exists_mulEquiv [Finite F₁'] [Finite F₂'] (S : Shape Y F₁ F₂) (S' : Shape Y' F₁' F₂')
    (σ₁ : F₁ ≃+* F₁') (σ₂ : F₂ ≃+* F₂') : Nonempty (Y ≃* Y') := by
  let T : Shape Y F₁' F₂' := ((S.mapField₁ σ₁).swap.mapField₁ σ₂).swap
  obtain ⟨E, u, hE⟩ := exists_conj_scalar S'.adm₁ T.adm₁
  let R₁ : Shape Y' F₁' F₂' := S'.recoord₁ E T.g₁ u hE
  obtain ⟨E₂, u₂, hE₂⟩ := exists_conj_scalar R₁.adm₂ T.adm₂
  let R₂ : Shape Y' F₁' F₂' := (R₁.swap.recoord₁ E₂ T.g₂ u₂ hE₂).swap
  exact mulEquiv_of_eq_g T R₂ rfl rfl

end Shape

section PGL

open Matrix.ProjGenLinGroup

theorem neg_one_mem_center : (-1 : SL(2, F)) ∈ Subgroup.center SL(2, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.scalar_apply]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem eq_one_or_neg_one_of_mem_center {B : SL(2, F)} (hB : B ∈ Subgroup.center SL(2, F)) :
    B = 1 ∨ B = -1 := by
  obtain ⟨r, hr, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hB
  have hr2 : r * r = 1 := by simpa [sq] using hr
  rcases mul_self_eq_one_iff.mp hr2 with rfl | rfl
  · left
    apply Subtype.ext
    rw [← hrB]; simp
  · right
    apply Subtype.ext
    rw [← hrB, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.scalar_apply]
    ext i j
    by_cases hij : i = j <;> simp [hij]

theorem mk_sq_eq_one {g : GL (Fin 2) F}
    (h : ∃ μ : F, (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = μ • 1) :
    (mk g : PGL(2, F)) * mk g = 1 := by
  obtain ⟨μ, hμ⟩ := h
  rw [← map_mul, mk_eq_one, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  exact ⟨μ, by rw [Units.val_mul, hμ, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem exists_sq_of_mk_eq_toPGL {g : GL (Fin 2) F} {A : SL(2, F)}
    (h : (mk g : PGL(2, F)) = Matrix.SpecialLinearGroup.toPGL A) :
    IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
  obtain ⟨u, hu⟩ := mk_eq_mk_iff.mp (h.trans rfl : (mk g : PGL(2, F)) = mk (Matrix.SpecialLinearGroup.toGL A))
  have hdet := congrArg (fun x : GL (Fin 2) F => ((Matrix.GeneralLinearGroup.det x : Fˣ) : F)) hu
  simp only [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.det_scalar, det_toGL,
    Fintype.card_fin] at hdet
  refine ⟨(u : F)⁻¹, ?_⟩
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  field_simp
  simp only [Units.val_pow_eq_pow_val] at hdet
  linear_combination hdet

theorem exists_toPGL_of_isSquare_det {g : GL (Fin 2) F}
    (h : IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) :
    ∃ A : SL(2, F), (mk g : PGL(2, F)) = Matrix.SpecialLinearGroup.toPGL A := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    intro h0
    have := (Matrix.GeneralLinearGroup.det g).ne_zero
    apply this; rw [hr, h0]; ring
  let A : SL(2, F) := ⟨r⁻¹ • (g : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_smul, ← Matrix.GeneralLinearGroup.val_det_apply, hr]
    simp [Fintype.card_fin]
    field_simp⟩
  refine ⟨A, ?_⟩
  show (mk g : PGL(2, F)) = mk (Matrix.SpecialLinearGroup.toGL A)
  rw [mk_eq_mk_iff]
  refine ⟨Units.mk0 r⁻¹ (inv_ne_zero hr0), ?_⟩
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, A, Units.val_mk0]
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  rfl

end PGL

section PGLHom

open Matrix.ProjGenLinGroup

theorem toPGL_conjSLAut (g : GL (Fin 2) F) (B : SL(2, F)) :
    Matrix.SpecialLinearGroup.toPGL (conjSLAut g B) =
      mk g * Matrix.SpecialLinearGroup.toPGL B * (mk g)⁻¹ := by
  show mk (Matrix.SpecialLinearGroup.toGL (conjSLAut g B)) = _
  rw [toGL_conjSLAut]
  simp [map_mul, map_inv]

variable {F₁ F₂ : Type} [Field F₁] [Field F₂] {Y : Type} [Group Y]

@[expose] noncomputable def thetaP (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂)
    (h₁ : ∃ μ : F₁, (g₁ : Matrix (Fin 2) (Fin 2) F₁) * (g₁ : Matrix (Fin 2) (Fin 2) F₁) = μ • 1)
    (h₂ : ∃ μ : F₂, (g₂ : Matrix (Fin 2) (Fin 2) F₂) * (g₂ : Matrix (Fin 2) (Fin 2) F₂) = μ • 1) :
    Pgrp g₁ g₂ h₁ h₂ →* PGL(2, F₂) :=
  SemidirectProduct.lift ((Matrix.SpecialLinearGroup.toPGL).comp (MonoidHom.snd _ _))
    (sgnHom (mk g₂) (mk_sq_eq_one h₂)) (by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · ext ⟨A, B⟩
      simp [phi, sgnHom_one]
    · ext ⟨A, B⟩
      simp [phi, sgnHom_neg_one, alphaAut_apply, toGL_conjSLAut, map_mul, map_inv])

theorem thetaP_apply (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂) (h₁ h₂) (x : Pgrp g₁ g₂ h₁ h₂) :
    thetaP g₁ g₂ h₁ h₂ x = Matrix.SpecialLinearGroup.toPGL x.left.2 *
      sgnHom (mk g₂) (mk_sq_eq_one h₂) x.right := rfl

end PGLHom

section PGLQuotient

open Matrix.ProjGenLinGroup

theorem liftOfSurjective_apply' {G H K : Type*} [Group G] [Group H] [Group K] (f : G →* H)
    (hf : Function.Surjective f) (g : G →* K) (hg : f.ker ≤ g.ker) (x : G) :
    (MonoidHom.liftOfSurjective f hf ⟨g, hg⟩) (f x) = g x := by
  simp [MonoidHom.liftOfSurjective]

variable {F₁ F₂ : Type} [Field F₁] [Field F₂] {Y : Type} [Group Y]

theorem thetaP_surjective [Finite F₂] (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂) (h₁ h₂)
    (hg : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g₂ : F₂ˣ) : F₂)) :
    Function.Surjective (thetaP g₁ g₂ h₁ h₂) := by
  intro q
  induction q using Matrix.ProjGenLinGroup.induction_on with | mk h =>
  by_cases hsq : IsSquare ((Matrix.GeneralLinearGroup.det h : F₂ˣ) : F₂)
  · obtain ⟨A, hA⟩ := exists_toPGL_of_isSquare_det hsq
    refine ⟨⟨(1, A), 1⟩, ?_⟩
    rw [thetaP_apply]
    simp [sgnHom_one, hA]
  · obtain ⟨w, hw0, hw⟩ := exists_mul_sq_of_not_isSquare hg hsq
    have hsq' : IsSquare ((Matrix.GeneralLinearGroup.det (h * g₂⁻¹) : F₂ˣ) : F₂) := by
      refine ⟨w, ?_⟩
      rw [map_mul, map_inv, Units.val_mul, hw]
      have : ((Matrix.GeneralLinearGroup.det g₂ : F₂ˣ) : F₂) *
          (((Matrix.GeneralLinearGroup.det g₂ : F₂ˣ)⁻¹ : F₂ˣ) : F₂) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc (w ^ 2 * ((Matrix.GeneralLinearGroup.det g₂ : F₂ˣ) : F₂)) *
          (((Matrix.GeneralLinearGroup.det g₂ : F₂ˣ)⁻¹ : F₂ˣ) : F₂)
          = w ^ 2 * (((Matrix.GeneralLinearGroup.det g₂ : F₂ˣ) : F₂) *
            (((Matrix.GeneralLinearGroup.det g₂ : F₂ˣ)⁻¹ : F₂ˣ) : F₂)) := by ring
        _ = w * w := by rw [this]; ring
    obtain ⟨A, hA⟩ := exists_toPGL_of_isSquare_det hsq'
    refine ⟨⟨(1, A), -1⟩, ?_⟩
    rw [thetaP_apply]
    simp only [sgnHom_neg_one]
    show Matrix.SpecialLinearGroup.toPGL A * mk g₂ = mk h
    rw [← hA, ← map_mul]
    congr 1
    group

namespace Shape

variable (S : Shape Y F₁ F₂)

theorem exists_pglHom [Finite F₂] :
    ∃ π : Y →* PGL(2, F₂), Function.Surjective π ∧ π.ker = S.I₁ := by
  have hψ := S.psi_surjective S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ rfl rfl
  have hker : (S.psi S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ rfl rfl).ker ≤
      (thetaP S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂).ker := by
    rw [S.ker_psi S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ rfl rfl, Subgroup.zpowers_le,
      MonoidHom.mem_ker]
    rw [kappa, thetaP_apply]
    show Matrix.SpecialLinearGroup.toPGL (-1 : SL(2, F₂)) *
      sgnHom (Matrix.ProjGenLinGroup.mk S.g₂) (mk_sq_eq_one S.sq_scalar₂) 1 = 1
    rw [sgnHom_one, mul_one, ← MonoidHom.mem_ker, Matrix.SpecialLinearGroup.toPGL_ker]
    exact neg_one_mem_center
  set π := MonoidHom.liftOfSurjective (S.psi S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ rfl rfl) hψ
    ⟨thetaP S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂, hker⟩ with hπdef
  have hπ : ∀ x, π (S.psi S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ rfl rfl x) =
      thetaP S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ x := fun x =>
    liftOfSurjective_apply' _ hψ _ hker x
  refine ⟨π, ?_, ?_⟩
  · intro q
    obtain ⟨x, hx⟩ := thetaP_surjective S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ S.ns₂ q
    exact ⟨S.psi S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ rfl rfl x, by rw [hπ, hx]⟩
  · apply le_antisymm
    · intro y hy
      obtain ⟨⟨⟨A, B⟩, u⟩, rfl⟩ := hψ y
      rw [MonoidHom.mem_ker, hπ, thetaP_apply] at hy
      rcases Int.units_eq_one_or u with rfl | rfl
      · simp only [sgnHom_one, mul_one] at hy
        have hB : B ∈ Subgroup.center SL(2, F₂) := by
          rw [← Matrix.SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker]; exact hy
        rw [Shape.psi_apply, sgnHom_one, mul_one, fnHom_apply]
        refine Subgroup.mul_mem _ (S.e₁.symm A).2 ?_
        rcases eq_one_or_neg_one_of_mem_center hB with rfl | rfl
        · simp
        · rw [S.symm_neg_one₂]; exact S.z_mem₁
      · exfalso
        simp only [sgnHom_neg_one] at hy
        have : (Matrix.ProjGenLinGroup.mk S.g₂ : PGL(2, F₂)) = Matrix.SpecialLinearGroup.toPGL B⁻¹ := by
          rw [map_inv]
          exact eq_inv_of_mul_eq_one_right hy
        exact S.ns₂ (exists_sq_of_mk_eq_toPGL this)
    · intro a ha
      rw [MonoidHom.mem_ker]
      have : a = S.psi S.g₁ S.g₂ S.sq_scalar₁ S.sq_scalar₂ rfl rfl ⟨(S.e₁ ⟨a, ha⟩, 1), 1⟩ := by
        rw [Shape.psi_apply, sgnHom_one, mul_one, fnHom_apply]
        simp
      rw [this, hπ, thetaP_apply]
      simp

end Shape

end PGLQuotient

section Charts

variable {F₁ F₂ : Type} [Field F₁] [Field F₂] {Y : Type} [Group Y]

@[expose] def Shape.ofCharts (fA : SL(2, F₁) →* Y) (fB : SL(2, F₂) →* Y)
    (hA : Function.Injective fA) (hB : Function.Injective fB)
    (hcomm : ∀ A B, fA A * fB B = fB B * fA A) (z : Y) (hzA : fA (-1) = z) (hzB : fB (-1) = z)
    (hz_sq : z * z = 1) (hz_ne : z ≠ 1) (hinter : ∀ A B, fA A = fB B → fA A = 1 ∨ fA A = z)
    (t : Y) (ht : t * t = 1) (hgen : fA.range ⊔ fB.range ⊔ Subgroup.zpowers t = ⊤)
    (g₁ : GL (Fin 2) F₁) (g₂ : GL (Fin 2) F₂)
    (hn₁ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g₁ : F₁ˣ) : F₁))
    (hn₂ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g₂ : F₂ˣ) : F₂))
    (hact₁ : ∀ A, t * fA A * t⁻¹ = fA (conjSLAut g₁ A))
    (hact₂ : ∀ B, t * fB B * t⁻¹ = fB (conjSLAut g₂ B)) : Shape Y F₁ F₂ where
  I₁ := fA.range
  I₂ := fB.range
  z := z
  t := t
  e₁ := (MonoidHom.ofInjective hA).symm
  e₂ := (MonoidHom.ofInjective hB).symm
  g₁ := g₁
  g₂ := g₂
  comm := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact hcomm A B
  inter := by
    apply le_antisymm
    · rintro y ⟨⟨A, rfl⟩, ⟨B, hB'⟩⟩
      rcases hinter A B hB'.symm with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers z
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨(-1), hzA⟩, ⟨(-1), hzB⟩⟩
  z_sq := hz_sq
  z_ne := hz_ne
  gen := hgen
  t_sq := ht
  ns₁ := hn₁
  ns₂ := hn₂
  act₁ := by
    rintro ⟨_, A, rfl⟩
    refine ⟨⟨fA (conjSLAut g₁ A), conjSLAut g₁ A, rfl⟩, ?_, ?_⟩
    · exact (hact₁ A).symm
    · have e1 : (MonoidHom.ofInjective hA).symm ⟨fA A, A, rfl⟩ = A := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      have e2 : (MonoidHom.ofInjective hA).symm ⟨fA (conjSLAut g₁ A), conjSLAut g₁ A, rfl⟩ =
          conjSLAut g₁ A := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      rw [e1, e2]
      rfl
  act₂ := by
    rintro ⟨_, B, rfl⟩
    refine ⟨⟨fB (conjSLAut g₂ B), conjSLAut g₂ B, rfl⟩, ?_, ?_⟩
    · exact (hact₂ B).symm
    · have e1 : (MonoidHom.ofInjective hB).symm ⟨fB B, B, rfl⟩ = B := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      have e2 : (MonoidHom.ofInjective hB).symm ⟨fB (conjSLAut g₂ B), conjSLAut g₂ B, rfl⟩ =
          conjSLAut g₂ B := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      rw [e1, e2]
      rfl

end Charts

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
