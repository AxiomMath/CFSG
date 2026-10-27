module

public import CFSG.GH74.GLS.IVK.L2.SLAut
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.Defs2

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank

section LangSL

variable {F : Type} [Field F] [Finite F]

noncomputable abbrev slσ (σ : F ≃+* F) : SL2 F ≃* SL2 F :=
  stableAut (StatedSL 2 F) (fieldStable_statedSL 2) σ

@[expose] noncomputable def slNegOne (F : Type) [Field F] : SL2 F :=
  ⟨-1, Subgroup.subset_closure (by
    show ((-1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1
    simp [Matrix.det_neg])⟩

end LangSL

namespace LangC

section Basic

variable {F : Type} [Field F]

theorem mem_sl_iff {g : GL (Fin 2) F} :
    g ∈ StatedSL 2 F ↔ (g : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem det_sl (g : SL2 F) : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  mem_sl_iff.1 g.2

theorem sl_ext {g h : SL2 F}
    (e : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) : g = h :=
  Subtype.ext (Units.ext e)

@[expose] def toSL (g : GL (Fin 2) F) (hg : (g : Matrix (Fin 2) (Fin 2) F).det = 1) : SL2 F :=
  ⟨g, mem_sl_iff.2 hg⟩

@[simp] theorem toSL_coe (g : GL (Fin 2) F) (hg : (g : Matrix (Fin 2) (Fin 2) F).det = 1) :
    ((toSL g hg : SL2 F) : GL (Fin 2) F) = g := rfl

@[simp] theorem slNegOne_coe : ((slNegOne F : SL2 F) : GL (Fin 2) F) = -1 := rfl

theorem slNegOne_mat :
    (((slNegOne F : SL2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  rw [slNegOne_coe]; rfl

@[simp] theorem slσ_coe (σ : F ≃+* F) (g : SL2 F) :
    ((slσ σ g : SL2 F) : GL (Fin 2) F) = glAut σ (g : GL (Fin 2) F) := rfl

theorem slσ_mat (σ : F ≃+* F) (g : SL2 F) :
    (((slσ σ g : SL2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map σ := rfl

theorem sl_mat_mul (g h : SL2 F) :
    (((g * h : SL2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl

theorem sl_mat_one : (((1 : SL2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := rfl

@[expose] noncomputable def slDiag (l : F) (hl : l ≠ 0) : SL2 F :=
  toSL (Matrix.GeneralLinearGroup.mkOfDetNeZero !![l, 0; 0, l⁻¹]
    (by simp [Matrix.det_fin_two, hl])) (by simp [Matrix.det_fin_two, hl])

theorem slDiag_mat (l : F) (hl : l ≠ 0) :
    (((slDiag l hl : SL2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![l, 0; 0, l⁻¹] := rfl

theorem apply_apply_of_orderOf (σ : F ≃+* F) (hσ : orderOf σ = 2) (x : F) : σ (σ x) = x := by
  have h1 : σ ^ 2 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have := congrArg (fun τ : F ≃+* F => τ x) h1
  simpa [pow_two] using this

theorem scalar_of_commute_slσ (σ : F ≃+* F) (m : GL (Fin 2) F)
    (hm : ∀ x : SL2 F, m * ((slσ σ x : SL2 F) : GL (Fin 2) F) =
      ((slσ σ x : SL2 F) : GL (Fin 2) F) * m) :
    ∃ s : F, (m : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
  apply exists_smul_one_of_commute_sl
  intro b
  set y : SL2 F := specialLinearGroupEquivStatedSL 2 F b with hy
  have h1 := hm ((slσ σ).symm y)
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h1
  have hyb : ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (b : Matrix (Fin 2) (Fin 2) F) :=
    specialLinearGroupEquivStatedSL_coe 2 F b
  simpa [hyb] using h2

end Basic

section GLAux

variable {F : Type} [Field F]

@[expose] noncomputable def glScal (l : F) (hl : l ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (l • (1 : Matrix (Fin 2) (Fin 2) F))
    (by simp [hl])

theorem glScal_coe (l : F) (hl : l ≠ 0) :
    ((glScal l hl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      l • (1 : Matrix (Fin 2) (Fin 2) F) := rfl

theorem glScal_central (l : F) (hl : l ≠ 0) (x : GL (Fin 2) F) :
    glScal l hl * x = x * glScal l hl := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, glScal_coe, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

@[expose] noncomputable def glDiag (a : F) (ha : a ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, 1] (by simp [Matrix.det_fin_two, ha])

theorem glDiag_coe (a : F) (ha : a ≠ 0) :
    ((glDiag a ha : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, 1] := rfl

theorem det_inv_gl (B : GL (Fin 2) F) :
    ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      ((B : Matrix (Fin 2) (Fin 2) F).det)⁻¹ := by
  have h : ((B : Matrix (Fin 2) (Fin 2) F).det) *
      ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  exact eq_inv_of_mul_eq_one_right h

theorem det_ne_zero_gl (B : GL (Fin 2) F) : (B : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero

theorem det_glAut (σ : F ≃+* F) (B : GL (Fin 2) F) :
    ((glAut σ B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      σ ((B : Matrix (Fin 2) (Fin 2) F).det) :=
  (RingHom.map_det σ.toRingHom (B : Matrix (Fin 2) (Fin 2) F)).symm

theorem speiser_gl (σ : F ≃+* F) (hσ : orderOf σ = 2) (A : GL (Fin 2) F)
    (hA : A * glAut σ A = 1) : ∃ B : GL (Fin 2) F, A * glAut σ B = B := by
  have hAi : CFSG.GH74.GLS.IVK.H90.Ai σ (A : Matrix (Fin 2) (Fin 2) F) 2 = 1 := by
    have h1 : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F).map σ = 1 :=
      congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hA
    simp only [CFSG.GH74.GLS.IVK.H90.Ai]
    rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.mul_one]
    exact h1
  obtain ⟨B, hB, hAB⟩ := CFSG.GH74.GLS.IVK.H90.speiser σ (A : Matrix (Fin 2) (Fin 2) F) 2 hσ
    (by norm_num) hAi
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B hB, ?_⟩
  apply Units.ext
  rw [Units.val_mul]
  exact hAB

theorem gl_cocycle_orbit (σ : F ≃+* F) (hσ : orderOf σ = 2) (A A' : GL (Fin 2) F)
    (hA : A * glAut σ A = 1) (hA' : A' * glAut σ A' = 1)
    (hdet : (A : Matrix (Fin 2) (Fin 2) F).det = (A' : Matrix (Fin 2) (Fin 2) F).det) :
    ∃ h : GL (Fin 2) F, (h : Matrix (Fin 2) (Fin 2) F).det = 1 ∧
      h * A * (glAut σ h)⁻¹ = A' := by
  obtain ⟨B, hB⟩ := speiser_gl σ hσ A hA
  obtain ⟨B', hB'⟩ := speiser_gl σ hσ A' hA'
  set a : F := (A : Matrix (Fin 2) (Fin 2) F).det with ha
  have ha0 : a ≠ 0 := det_ne_zero_gl A
  set μ : F := (B : Matrix (Fin 2) (Fin 2) F).det with hμ
  set μ' : F := (B' : Matrix (Fin 2) (Fin 2) F).det with hμ'
  have hμ0 : μ ≠ 0 := det_ne_zero_gl B
  have hμ'0 : μ' ≠ 0 := det_ne_zero_gl B'
  have hrel : a * σ μ = μ := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F).det) hB
    simp only [Units.val_mul, Matrix.det_mul, det_glAut] at this
    exact this
  have hrel' : a * σ μ' = μ' := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F).det) hB'
    simp only [Units.val_mul, Matrix.det_mul, det_glAut] at this
    rw [← hdet] at this
    exact this
  set ν : F := μ' / μ with hν
  have hν0 : ν ≠ 0 := div_ne_zero hμ'0 hμ0
  have hσν : σ ν = ν := by
    have hσμ0 : σ μ ≠ 0 := fun h => hμ0 (σ.injective (by simpa using h))
    rw [hν, map_div₀, div_eq_div_iff hσμ0 hμ0]
    apply mul_left_cancel₀ ha0
    linear_combination μ * hrel' - μ' * hrel
  set g : GL (Fin 2) F := glDiag ν⁻¹ (inv_ne_zero hν0) with hg
  have hgfix : glAut σ g = g := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hg, glDiag_coe, glAut_coe, hσν]
  refine ⟨B' * g * B⁻¹, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_inv_gl, hg, glDiag_coe]
    simp only [Matrix.det_fin_two_of, mul_zero, sub_zero, mul_one]
    rw [← hμ, ← hμ', hν]
    field_simp
  · have hAeq : A = B * (glAut σ B)⁻¹ := eq_mul_inv_of_mul_eq hB
    have hA'eq : A' = B' * (glAut σ B')⁻¹ := eq_mul_inv_of_mul_eq hB'
    rw [hA'eq, hAeq, map_mul, map_mul, map_inv, hgfix]
    group

end GLAux

end LangC

section LangSL

open LangC

variable {F : Type} [Field F] [Finite F]

theorem exists_cocycle_neg (hodd : Odd (Nat.card F)) (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    ∃ k : SL2 F, k * slσ σ k = slNegOne F := by
  have _ := hodd
  have hfix : σ (-1 : F) = -1 := by simp
  have hne : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  obtain ⟨l, hl0, hl⟩ := CFSG.GH74.GLS.IVK.H90.exists_prod_pow_eq σ (-1) hfix hne
  rw [hσ] at hl
  simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, pow_zero,
    pow_one] at hl
  refine ⟨slDiag l hl0, ?_⟩
  apply sl_ext
  rw [sl_mat_mul, slσ_mat, slDiag_mat, slNegOne_mat]
  have hl' : l * σ l = -1 := by simpa using hl
  have hσl : σ l ≠ 0 := fun h => hl0 (σ.injective (by simpa using h))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hl']
  rw [← mul_inv, hl']
  simp

theorem cocycle_orbit (hodd : Odd (Nat.card F)) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    {ε : SL2 F} (hε : ε = 1 ∨ ε = slNegOne F) {k k' : SL2 F}
    (hk : k * slσ σ k = ε) (hk' : k' * slσ σ k' = ε) :
    ∃ h : SL2 F, k' = h * k * (slσ σ h)⁻¹ := by
  have _ := hodd
  obtain ⟨e, he1, he, hεmat⟩ : ∃ e : F, e * e = 1 ∧ σ e = e ∧
      (((ε : SL2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        e • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rcases hε with rfl | rfl
    · exact ⟨1, by simp, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp, by rw [slNegOne_mat]; simp⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he1
  obtain ⟨l, hl0, hl⟩ := CFSG.GH74.GLS.IVK.H90.exists_prod_pow_eq σ e he he0
  rw [hσ] at hl
  simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, pow_zero,
    pow_one] at hl
  have hl' : l * σ l = e := by simpa using hl
  set s : GL (Fin 2) F := glScal l hl0 with hs
  have hKK : ∀ x : SL2 F, x * slσ σ x = ε →
      (((x : SL2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (((x : SL2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map σ =
          e • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro x hx
    have := congrArg (fun y : SL2 F => ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hx
    rw [← hεmat]
    exact this
  have hAm : ∀ x : SL2 F,
      ((s * (x : GL (Fin 2) F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        l • ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro x
    rw [Units.val_mul, hs, glScal_coe, Matrix.smul_mul, Matrix.one_mul]
  have hAσ : ∀ x : SL2 F,
      ((glAut σ (s * (x : GL (Fin 2) F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        σ l • ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map σ := by
    intro x
    show ((s * (x : GL (Fin 2) F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map σ = _
    rw [hAm, Matrix.map_smul' σ l _ (map_mul σ)]
  have hcoc : ∀ x : SL2 F, x * slσ σ x = ε →
      (s * (x : GL (Fin 2) F)) * glAut σ (s * (x : GL (Fin 2) F)) = 1 := by
    intro x hx
    apply Units.ext
    rw [Units.val_mul, hAm, hAσ, smul_mul_smul_comm, hl', hKK x hx, smul_smul, he1, one_smul]
    rfl
  have hdetA : ∀ x : SL2 F,
      ((s * (x : GL (Fin 2) F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = l ^ 2 := by
    intro x
    rw [hAm, Matrix.det_smul, det_sl x, Fintype.card_fin, mul_one]
  obtain ⟨h₀, hdet1, hh⟩ := gl_cocycle_orbit σ hσ (s * (k : GL (Fin 2) F))
    (s * (k' : GL (Fin 2) F)) (hcoc k hk) (hcoc k' hk') (by rw [hdetA, hdetA])
  refine ⟨toSL h₀ hdet1, ?_⟩
  apply Subtype.ext
  show (k' : GL (Fin 2) F) = h₀ * (k : GL (Fin 2) F) * (glAut σ h₀)⁻¹
  apply mul_left_cancel (a := s)
  have hc : h₀ * s = s * h₀ := (glScal_central l hl0 h₀).symm
  calc s * (k' : GL (Fin 2) F) = h₀ * (s * (k : GL (Fin 2) F)) * (glAut σ h₀)⁻¹ := hh.symm
    _ = (h₀ * s) * (k : GL (Fin 2) F) * (glAut σ h₀)⁻¹ := by simp only [mul_assoc]
    _ = (s * h₀) * (k : GL (Fin 2) F) * (glAut σ h₀)⁻¹ := by rw [hc]
    _ = s * (h₀ * (k : GL (Fin 2) F) * (glAut σ h₀)⁻¹) := by simp only [mul_assoc]

theorem exists_twist_neg_one (hodd : Odd (Nat.card F)) (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    ∃ h : SL2 F, h * (slσ σ h)⁻¹ = slNegOne F := by
  have _ := hodd
  have _hfin : Finite (F ≃+* F) := CFSG.GH74.GLS.IVK.finite_ringEquiv F
  have hσ2 : ∀ x : F, σ (σ x) = x := apply_apply_of_orderOf σ hσ
  have hne1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    omega
  obtain ⟨x, hx⟩ : ∃ x : F, σ x ≠ x := by
    by_contra hcon
    exact hne1 (RingEquiv.ext fun y => not_not.1 fun h => hcon ⟨y, h⟩)
  obtain ⟨ι, hι0, hσι⟩ : ∃ ι : F, ι ≠ 0 ∧ σ ι = -ι :=
    ⟨x - σ x, fun h => hx (by linear_combination -h), by rw [map_sub, hσ2]; ring⟩
  refine ⟨slDiag ι hι0, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply sl_ext
  rw [sl_mat_mul, slσ_mat, slDiag_mat, slNegOne_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hσι]

theorem sign_lemma_cocycle (hodd : Odd (Nat.card F)) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    (d : GL (Fin 2) F) (hd : ¬ IsSquare ((d : Matrix (Fin 2) (Fin 2) F).det)) (c : SL2 F)
    (hc : ∀ x : SL2 F, d * ((slσ σ x : SL2 F) : GL (Fin 2) F) * d⁻¹ =
      (c : GL (Fin 2) F) * glAut σ d * ((slσ σ x : SL2 F) : GL (Fin 2) F) * (glAut σ d)⁻¹ *
        (c : GL (Fin 2) F)⁻¹) :
    c * slσ σ c = slNegOne F := by
  have hF2 : (2 : F) ≠ 0 :=
    Ring.two_ne_zero (CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hodd)
  have hσ2 : ∀ x : F, σ (σ x) = x := apply_apply_of_orderOf σ hσ
  set p : GL (Fin 2) F := (c : GL (Fin 2) F) * glAut σ d with hp
  have hcomm : ∀ x : SL2 F, (p⁻¹ * d) * ((slσ σ x : SL2 F) : GL (Fin 2) F) =
      ((slσ σ x : SL2 F) : GL (Fin 2) F) * (p⁻¹ * d) := by
    intro x
    have h := hc x
    have h' : d * ((slσ σ x : SL2 F) : GL (Fin 2) F) * d⁻¹ =
        p * ((slσ σ x : SL2 F) : GL (Fin 2) F) * p⁻¹ := by
      rw [h, hp]; group
    calc (p⁻¹ * d) * ((slσ σ x : SL2 F) : GL (Fin 2) F)
        = p⁻¹ * (d * ((slσ σ x : SL2 F) : GL (Fin 2) F) * d⁻¹) * d := by group
      _ = p⁻¹ * (p * ((slσ σ x : SL2 F) : GL (Fin 2) F) * p⁻¹) * d := by rw [h']
      _ = ((slσ σ x : SL2 F) : GL (Fin 2) F) * (p⁻¹ * d) := by group
  obtain ⟨s, hs⟩ := scalar_of_commute_slσ σ (p⁻¹ * d) hcomm
  set D : Matrix (Fin 2) (Fin 2) F := (d : Matrix (Fin 2) (Fin 2) F) with hDdef
  set C : Matrix (Fin 2) (Fin 2) F := ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hCdef
  have hD : D = s • (C * D.map σ) := by
    have h1 : d = p * (p⁻¹ * d) := by group
    have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h1
    rw [Units.val_mul, hs, Matrix.mul_smul, Matrix.mul_one] at h2
    exact h2
  have hCdet : C.det = 1 := det_sl c
  have hDσdet : (D.map σ).det = σ D.det := (RingHom.map_det σ.toRingHom D).symm
  have hμ0 : D.det ≠ 0 := det_ne_zero_gl d
  have hμ : D.det = s ^ 2 * σ D.det := by
    have := congrArg Matrix.det hD
    rw [Matrix.det_smul, Matrix.det_mul, hCdet, hDσdet, Fintype.card_fin, one_mul] at this
    exact this
  have hDD : (D.map σ).map σ = D := by
    ext i j
    simp [Matrix.map_apply, hσ2]
  have hDσ : D.map σ = σ s • (C.map σ * D) := by
    have h1 := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X.map σ) hD
    have hmap : ∀ M N : Matrix (Fin 2) (Fin 2) F, (M * N).map σ = M.map σ * N.map σ :=
      fun M N => Matrix.map_mul (f := σ.toRingHom)
    rw [Matrix.map_smul' σ s _ (map_mul σ), hmap] at h1
    have h2 : (C.map σ * (D.map σ).map σ) = C.map σ * D := by rw [hDD]
    rw [← h2]
    exact h1
  have hN1 : (s * σ s) • (C * C.map σ) = 1 := by
    have h1 : D = (s * σ s) • ((C * C.map σ) * D) := by
      conv_lhs => rw [hD, hDσ]
      rw [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    have h2 : D * ((d⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [hDdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h3 := congrArg (fun X : Matrix (Fin 2) (Fin 2) F =>
      X * ((d⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h1
    rw [h2, Matrix.smul_mul, Matrix.mul_assoc, h2, Matrix.mul_one] at h3
    exact h3.symm
  have hσμ : σ D.det = σ s ^ 2 * D.det := by
    have h1 := congrArg σ hμ
    rw [map_mul, map_pow, hσ2] at h1
    exact h1
  have hN2 : (s * σ s) * (s * σ s) = 1 := by
    have h1 : D.det * ((s * σ s) ^ 2 - 1) = 0 := by
      linear_combination (-1) * hμ - s ^ 2 * hσμ
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hμ0
    · linear_combination h
  rcases mul_self_eq_one_iff.1 hN2 with hN | hN
  ·
    exfalso
    apply hd
    have hφ : σ (s * σ D.det) = s * σ D.det := by
      rw [map_mul, hσ2]
      linear_combination (σ s) * hμ + (s * σ D.det) * hN
    have hφ2 : (s * σ D.det) ^ 2 = ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) D.det := by
      rw [hσ]
      simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, pow_zero,
        pow_one]
      have : ((1 : F ≃+* F) D.det) = D.det := rfl
      rw [this]
      linear_combination (-(σ D.det)) * hμ
    exact CFSG.GH74.GLS.IVK.isSquare_of_prod_fixed_sq hF2 σ hμ0 hφ hφ2
  · apply sl_ext
    rw [sl_mat_mul, slσ_mat, slNegOne_mat]
    rw [hN] at hN1
    rw [neg_smul, one_smul, neg_eq_iff_eq_neg] at hN1
    exact hN1

end LangSL

end CFSG.GH74.GLS.IVK.Prod3
