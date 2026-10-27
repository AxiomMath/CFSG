module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabL

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag Blocks
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open scoped commutatorElement

variable {F : Type} [Field F]

theorem transpose_comm_stdJ {X : Matrix (Fin 4) (Fin 4) F} (h : X * stdJ = stdJ * X) :
    Xᵀ * stdJ = stdJ * Xᵀ := by
  have hJ : (stdJ : Matrix (Fin 4) (Fin 4) F)ᵀ = -stdJ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [stdJ]
  have := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ, Matrix.mul_neg, Matrix.neg_mul] at this
  exact (neg_inj.1 this).symm

theorem comm_smul_add_smul {Y : Matrix (Fin 4) (Fin 4) F} (h : Y * stdJ = stdJ * Y) (a b : F) :
    (a • 1 + b • stdJ : Matrix (Fin 4) (Fin 4) F) * Y = Y * (a • 1 + b • stdJ) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, h]

theorem formA_mul_formA : (formA : Matrix (Fin 4) (Fin 4) F) * formA = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formA, Matrix.mul_apply, Fin.sum_univ_four]

theorem smul_add_smul_mul_comm (a b c d : F) :
    (a • 1 + b • stdJ : Matrix (Fin 4) (Fin 4) F) * (c • 1 + d • stdJ) =
      (c • 1 + d • stdJ) * (a • 1 + b • stdJ) := by
  rw [smul_add_smul_mul, smul_add_smul_mul]
  congr 1 <;> congr 1 <;> ring

theorem transpose_mul_formA_mul {X : Matrix (Fin 4) (Fin 4) F} (h : X * stdJ = stdJ * X) :
    ∃ α β : F, Xᵀ * formA * X = (α • 1 + β • stdJ) * formA := by
  have := mul_formA_mul_transpose (transpose_comm_stdJ h)
  rwa [Matrix.transpose_transpose] at this

variable (F) in
@[expose] noncomputable def mu : C₀ F →* Matrix (Fin 4) (Fin 4) F where
  toFun X := -(((X : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ * formA *
    ((X : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * formA)
  map_one' := by
    change -((1 : Matrix (Fin 4) (Fin 4) F)ᵀ * formA * 1 * formA) = 1
    rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, formA_mul_formA, neg_neg]
  map_mul' X Y := by
    set MX := ((X : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hMX
    set MY := ((Y : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hMY
    have hX : MX * stdJ = stdJ * MX := mem_C₀_iff.1 X.2
    have hY : MY * stdJ = stdJ * MY := mem_C₀_iff.1 Y.2
    obtain ⟨a, b, hab⟩ := transpose_mul_formA_mul hX
    obtain ⟨c, d, hcd⟩ := transpose_mul_formA_mul hY
    have hXY : (((X * Y : C₀ F) : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        MX * MY := rfl
    change -((((X * Y : C₀ F) : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
      formA * (((X * Y : C₀ F) : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        formA) = -(MXᵀ * formA * MX * formA) * -(MYᵀ * formA * MY * formA)
    rw [hXY, Matrix.transpose_mul]
    have hYt := transpose_comm_stdJ hY
    have hL : MYᵀ * MXᵀ * formA * (MX * MY) = (a • 1 + b • stdJ) * (c • 1 + d • stdJ) * formA :=
      calc MYᵀ * MXᵀ * formA * (MX * MY) = MYᵀ * (MXᵀ * formA * MX) * MY := by
            simp only [Matrix.mul_assoc]
        _ = (MYᵀ * (a • 1 + b • stdJ)) * formA * MY := by rw [hab]; simp only [Matrix.mul_assoc]
        _ = (a • 1 + b • stdJ) * (MYᵀ * formA * MY) := by
            rw [← comm_smul_add_smul hYt]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hcd, Matrix.mul_assoc]
    rw [hL, hab, hcd]
    simp only [Matrix.mul_assoc, formA_mul_formA, Matrix.mul_neg, Matrix.mul_one, neg_neg]

theorem transpose_mul_formA_mul_of_mu_eq_one {X : C₀ F} (h : mu F X = 1) :
    ((X : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ * formA *
      ((X : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = formA := by
  set MX := ((X : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hMX
  change -(MXᵀ * formA * MX * formA) = 1 at h
  calc MXᵀ * formA * MX = -(MXᵀ * formA * MX * formA) * formA := by
        rw [Matrix.neg_mul, Matrix.mul_assoc _ formA formA, formA_mul_formA, Matrix.mul_neg,
          Matrix.mul_one, neg_neg]
    _ = formA := by rw [h, Matrix.one_mul]

theorem mu_eq (X : C₀ F) : ∃ a b : F, mu F X = a • 1 + b • stdJ := by
  obtain ⟨a, b, hab⟩ := transpose_mul_formA_mul (mem_C₀_iff.1 X.2)
  refine ⟨a, b, ?_⟩
  change -(((X : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ * formA *
    ((X : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * formA) = _
  rw [hab, Matrix.mul_assoc, formA_mul_formA, Matrix.mul_neg, Matrix.mul_one, neg_neg]

theorem transpose_mul_formA_mul_of_mem_S₀ {u : SpecialLinearGroup (Fin 4) F} (hu : u ∈ S₀ F) :
    (u : Matrix (Fin 4) (Fin 4) F)ᵀ * formA * (u : Matrix (Fin 4) (Fin 4) F) = formA := by
  have hSC : S₀ F ≤ C₀ F := Subgroup.commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hle : S₀ F ≤ (mu F).ker.map (C₀ F).subtype := by
    rw [S₀, Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : C₀ F), (⟨b, hb⟩ : C₀ F)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul]
    obtain ⟨a₁, b₁, h1⟩ := mu_eq (⟨a, ha⟩ : C₀ F)
    obtain ⟨a₂, b₂, h2⟩ := mu_eq (⟨b, hb⟩ : C₀ F)
    obtain ⟨a₃, b₃, h3⟩ := mu_eq (⟨a, ha⟩ : C₀ F)⁻¹
    have hc : mu F ⟨b, hb⟩ * mu F (⟨a, ha⟩ : C₀ F)⁻¹ =
        mu F (⟨a, ha⟩ : C₀ F)⁻¹ * mu F ⟨b, hb⟩ := by
      rw [h2, h3, smul_add_smul_mul_comm]
    calc mu F ⟨a, ha⟩ * mu F ⟨b, hb⟩ * mu F (⟨a, ha⟩ : C₀ F)⁻¹ * mu F (⟨b, hb⟩ : C₀ F)⁻¹
        = mu F ⟨a, ha⟩ * (mu F ⟨b, hb⟩ * mu F (⟨a, ha⟩ : C₀ F)⁻¹) *
            mu F (⟨b, hb⟩ : C₀ F)⁻¹ := by rw [Matrix.mul_assoc (mu F ⟨a, ha⟩)]
      _ = mu F ((⟨a, ha⟩ : C₀ F) * (⟨a, ha⟩ : C₀ F)⁻¹) *
            mu F ((⟨b, hb⟩ : C₀ F) * (⟨b, hb⟩ : C₀ F)⁻¹) := by
          rw [hc, map_mul, map_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_inv_cancel, mul_inv_cancel, map_one, Matrix.one_mul]
  obtain ⟨y, hy, rfl⟩ := hle hu
  exact transpose_mul_formA_mul_of_mu_eq_one (MonoidHom.mem_ker.1 hy)

theorem conj_transpose_mul_mul {R G Gi X : Matrix (Fin 4) (Fin 4) F} (hGi : G * Gi = 1)
    (hX : Xᵀ * (Gᵀ * R * G) * X = Gᵀ * R * G) : (G * X * Gi)ᵀ * R * (G * X * Gi) = R := by
  have hT : Giᵀ * Gᵀ = 1 := by rw [← Matrix.transpose_mul, hGi, Matrix.transpose_one]
  calc (G * X * Gi)ᵀ * R * (G * X * Gi) = Giᵀ * (Xᵀ * (Gᵀ * R * G) * X) * Gi := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (Giᵀ * Gᵀ) * R * (G * Gi) := by rw [hX]; simp only [Matrix.mul_assoc]
    _ = R := by rw [hT, hGi, Matrix.one_mul, Matrix.mul_one]

variable [Fintype F]

omit [Fintype F] in
theorem exists_transpose_mul_mul_eq_formA (h2 : (2 : F) ≠ 0) {R : Matrix (Fin 4) (Fin 4) F}
    (hR : Rᵀ = -R) (hRu : IsUnit R.det) :
    ∃ P : Matrix (Fin 4) (Fin 4) F, IsUnit P.det ∧ Pᵀ * R * P = formA := by
  classical
  have halt : ∀ M : Matrix (Fin 4) (Fin 4) F, Mᵀ = -M → (toBilin' M).IsAlt := fun M hM v => by
    rw [Matrix.toBilin'_apply']
    exact dotProduct_mulVec_self_eq_zero h2 hM v
  have hnd : ∀ M : Matrix (Fin 4) (Fin 4) F, IsUnit M.det → (toBilin' M).Nondegenerate :=
    fun M hM => LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 hM.ne_zero
  obtain ⟨e⟩ := exists_form_isometry (toBilin' formA) (toBilin' R) (halt _ formA_transpose)
    (hnd _ (by rw [det_formA]; exact isUnit_one)) (halt _ hR) (hnd _ hRu) rfl
  set P := LinearMap.toMatrix' (e.toLinearEquiv : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) with hP
  refine ⟨P, ?_, ?_⟩
  · rw [hP, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' e.toLinearEquiv
  · apply Matrix.toBilin'.injective
    rw [← Matrix.toBilin'_comp, hP, Matrix.toLin'_toMatrix']
    refine LinearMap.BilinForm.ext fun x y => ?_
    rw [LinearMap.BilinForm.comp_apply]
    exact e.map_app y x

theorem exists_SL_transpose_mul_mul (h2 : (2 : F) ≠ 0) (hF : Fintype.card F % 2 = 1)
    {R : Matrix (Fin 4) (Fin 4) F} (hR : Rᵀ = -R) (hRu : IsUnit R.det) :
    ∃ (g₀ : SpecialLinearGroup (Fin 4) F) (α β : F),
      (g₀ : Matrix (Fin 4) (Fin 4) F)ᵀ * R * (g₀ : Matrix (Fin 4) (Fin 4) F) =
        (α • 1 + β • stdJ) * formA := by
  obtain ⟨P, hPu, hP⟩ := exists_transpose_mul_mul_eq_formA h2 hR hRu
  obtain ⟨a, c, hac⟩ := exists_sq_add_sq' hF (P.det)⁻¹
  have hdet : (P * stdD a c).det = 1 := by
    rw [Matrix.det_mul, det_stdD, hac, mul_inv_cancel₀ hPu.ne_zero]
  obtain ⟨α, β, hab⟩ := transpose_mul_formA_mul (stdD_mul_stdJ a c)
  refine ⟨⟨P * stdD a c, hdet⟩, α, β, ?_⟩
  change (P * stdD a c)ᵀ * R * (P * stdD a c) = _
  calc (P * stdD a c)ᵀ * R * (P * stdD a c) = (stdD a c)ᵀ * (Pᵀ * R * P) * stdD a c := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hP, hab]

theorem exists_fixed_conj_of_alternating (hF : Fintype.card F % 4 = 3) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    ∃ g₀ : SpecialLinearGroup (Fin 4) F,
      (∀ u ∈ S₀ F, (conjAut 4 F A * dualAut 4 F) (proj 4 F (g₀ * u * g₀⁻¹)) =
        proj 4 F (g₀ * u * g₀⁻¹)) ∧
      ∃ h : SpecialLinearGroup (Fin 4) F,
        (conjAut 4 F A * dualAut 4 F) (proj 4 F (g₀ * h * g₀⁻¹)) = proj 4 F (g₀ * h * g₀⁻¹) ∧
        (h : Matrix (Fin 4) (Fin 4) F) * stdJ ≠ stdJ * (h : Matrix (Fin 4) (Fin 4) F) ∧
        (h : Matrix (Fin 4) (Fin 4) F) * stdJ ≠ -(stdJ * (h : Matrix (Fin 4) (Fin 4) F)) := by
  have h2 := two_ne_zero_of_card_mod_four hF
  have hF2 : Fintype.card F % 2 = 1 := by omega
  set R := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hRdef
  have hAR : (A : Matrix (Fin 4) (Fin 4) F) * R = 1 := by
    rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRt : Rᵀ = -R := by
    have h1 : Rᵀ * (A : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one]
    rw [hA, Matrix.mul_neg, neg_eq_iff_eq_neg] at h1
    calc Rᵀ = Rᵀ * ((A : Matrix (Fin 4) (Fin 4) F) * R) := by rw [hAR, Matrix.mul_one]
      _ = -R := by rw [← Matrix.mul_assoc, h1, Matrix.neg_mul, Matrix.one_mul]
  have hRu : IsUnit R.det := by
    rw [hRdef, ← GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  obtain ⟨g₀, α, β, hg₀⟩ := exists_SL_transpose_mul_mul h2 hF2 hRt hRu
  set G := (g₀ : Matrix (Fin 4) (Fin 4) F) with hG
  set Gi := ((g₀⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hGi
  have hGGi : G * Gi = 1 :=
    congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
      (mul_inv_cancel g₀)
  have hfix : ∀ X : SpecialLinearGroup (Fin 4) F,
      (X : Matrix (Fin 4) (Fin 4) F)ᵀ * (Gᵀ * R * G) * (X : Matrix (Fin 4) (Fin 4) F) =
        Gᵀ * R * G →
      (conjAut 4 F A * dualAut 4 F) (proj 4 F (g₀ * X * g₀⁻¹)) = proj 4 F (g₀ * X * g₀⁻¹) := by
    intro X hX
    apply conjAut_dualAut_proj_of_transpose_mul_mul A
    exact conj_transpose_mul_mul hGGi hX
  refine ⟨g₀, fun u hu => hfix u ?_, ?_⟩
  · have hSC : S₀ F ≤ C₀ F := Subgroup.commutator_le.2 fun a ha b hb =>
      mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hut := transpose_comm_stdJ (mem_C₀_iff.1 (hSC hu))
    have hinv := transpose_mul_formA_mul_of_mem_S₀ hu
    rw [hg₀]
    calc (u : Matrix (Fin 4) (Fin 4) F)ᵀ * ((α • 1 + β • stdJ) * formA) *
          (u : Matrix (Fin 4) (Fin 4) F)
        = ((u : Matrix (Fin 4) (Fin 4) F)ᵀ * (α • 1 + β • stdJ)) * formA *
            (u : Matrix (Fin 4) (Fin 4) F) := by
          simp only [Matrix.mul_assoc]
      _ = (α • 1 + β • stdJ) * ((u : Matrix (Fin 4) (Fin 4) F)ᵀ * formA *
            (u : Matrix (Fin 4) (Fin 4) F)) := by
          rw [← comm_smul_add_smul hut]
          simp only [Matrix.mul_assoc]
      _ = (α • 1 + β • stdJ) * formA := by rw [hinv]
  · set R' := Gᵀ * R * G with hR'
    have hR't : R'ᵀ = -R' := by
      rw [hR', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hRt]
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    have hR'u : IsUnit R'.det := by
      rw [hR', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      have hGd : G.det = 1 := g₀.2
      rw [hGd, one_mul, mul_one]
      exact hRu
    obtain ⟨h₁, hdet, hh₁, hne1, hne2⟩ := exists_transvection h2 hR't hR'u
    have hdet' : h₁ᵀ.det = 1 := by rw [Matrix.det_transpose, hdet]
    have hJt : (stdJ : Matrix (Fin 4) (Fin 4) F)ᵀ = -stdJ := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [stdJ]
    refine ⟨⟨h₁ᵀ, hdet'⟩, hfix _ ?_, ?_, ?_⟩
    · change (h₁ᵀ)ᵀ * R' * h₁ᵀ = R'
      rw [Matrix.transpose_transpose]
      exact hh₁
    · intro hc
      apply hne1
      have := congrArg Matrix.transpose hc
      change (h₁ᵀ * stdJ)ᵀ = (stdJ * h₁ᵀ)ᵀ at this
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hJt,
        Matrix.mul_neg, Matrix.neg_mul] at this
      exact (neg_inj.1 this).symm
    · intro hc
      apply hne2
      have := congrArg Matrix.transpose hc
      change (h₁ᵀ * stdJ)ᵀ = (-(stdJ * h₁ᵀ))ᵀ at this
      rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, hJt, Matrix.mul_neg, Matrix.neg_mul, neg_neg] at this
      exact this.symm

end StabL

end CFSG.ComponentClassification.CatFactsL4U4
