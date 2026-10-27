module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsSigma
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndDefs

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ComponentClassification
open scoped MatrixGroups

section General

variable {n : ℕ} {F : Type} [Field F]

theorem isPrimeFormGram_revGL : IsPrimeFormGram (revGL n F) := by
  refine ⟨revGL_transpose, fun i j => ?_⟩
  rw [revGL_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem coe_stdSL_conjField (A : GL (Fin n) F) (φ : F ≃+* F) (x : SL(n, F)) :
    (stdSL n F A φ 0 x : Matrix (Fin n) (Fin n) F) =
      (A : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F).map φ *
        ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [stdSL, pow_zero, mul_one, MulAut.mul_apply,
    CatalogueBHigherLinearAction.slConjugation_matrix]
  rfl

end General

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem map_frobenius_eq_bar (h : UnitaryFieldData 2 1 F) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) F) :
    M.map (frobeniusEquiv F 2 : F →+* F) = M.map h.bar := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, RingEquiv.coe_toRingHom, frobeniusEquiv_apply,
    frobenius_def, h.bar_apply, pow_one]

theorem mem_msigma_iff (h : UnitaryFieldData 2 1 F) (x : SL(4, F)) :
    x ∈ YamadaEnd.msigma F ↔ SpecialLinearGroup.toGL x ∈
      gramSU h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [msigma_eq_slUnitary, mem_slUnitary, mem_gramSU, SpecialLinearGroup.coe_GL_coe_matrix,
    map_frobenius_eq_bar h]
  exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩

omit [Finite F] [CharP F 2] in
theorem normOneScalars_four_two_eq_bot (h : UnitaryFieldData 2 1 F)
    (G : Subgroup (GL (Fin 4) F)) : normOneScalars h G 4 = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨c, hcN, hc4, hz⟩ := hz
  have hc3 : c ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hcN, UnitaryFieldData.norm, h.bar_apply]
    ring
  have hc1 : c = 1 := by
    have h4 : c ^ 4 = c ^ 3 * c := pow_succ c 3
    rw [hc4, hc3, one_mul] at h4
    exact h4.symm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hz, hc1, map_one]
  rfl

noncomputable def msigmaToGramSU (h : UnitaryFieldData 2 1 F) :
    YamadaEnd.msigma F →* gramSU h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) where
  toFun x := ⟨SpecialLinearGroup.toGL (x : SL(4, F)), (mem_msigma_iff h _).mp x.2⟩
  map_one' := Subtype.ext (map_one SpecialLinearGroup.toGL)
  map_mul' x y := Subtype.ext (map_mul SpecialLinearGroup.toGL (x : SL(4, F)) y)

theorem msigmaToP_bijective (h : UnitaryFieldData 2 1 F) :
    Function.Bijective ((QuotientGroup.mk' (normOneScalars h (gramSU h
      ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) 4)).comp (msigmaToGramSU h)) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun x hx => ?_, fun q => ?_⟩
  · rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      normOneScalars_four_two_eq_bot, Subgroup.mem_bot] at hx
    apply Subtype.ext
    apply SpecialLinearGroup.toGL_injective
    rw [OneMemClass.coe_one, map_one]
    exact congrArg Subtype.val hx
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hg : SpecialLinearGroup.toGL (⟨((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F), g.2.2⟩ :
        SL(4, F)) = g := Units.ext rfl
    refine ⟨⟨⟨((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F), g.2.2⟩,
      (mem_msigma_iff h _).mpr (by rw [hg]; exact g.2)⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext hg

noncomputable def msigmaEquivP (h : UnitaryFieldData 2 1 F) :
    YamadaEnd.msigma F ≃* primeFormP h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
  MulEquiv.ofBijective _ (msigmaToP_bijective h)

theorem stdSL_conjField_sigma (h : UnitaryFieldData 2 1 F) {A : GL (Fin 4) F}
    (hA : A ∈ primeFormUnitary h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (φ : F ≃+* F) (x : SL(4, F)) :
    stdSL 4 F A φ 0 (YamadaEnd.sigmaSL F x) = YamadaEnd.sigmaSL F (stdSL 4 F A φ 0 x) := by
  set fr : F ≃+* F := frobeniusEquiv F 2
  set J := (revGL 4 F : Matrix (Fin 4) (Fin 4) F)
  set M := (A : Matrix (Fin 4) (Fin 4) F)
  set M' := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  set X := ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
  have hMM' : M * M' = 1 := Units.mul_inv A
  have hA' : (M.map fr)ᵀ * J * M = J := by
    rw [mem_primeFormUnitary, ← map_frobenius_eq_bar h] at hA
    exact hA
  have hJJ : J * J = 1 := revGL_mul_self
  have hJφ : J.map φ = J := revGL_map (φ : F →+* F)
  have h1 : (M.map fr)ᵀ * J = J * M' := by
    calc (M.map fr)ᵀ * J = (M.map fr)ᵀ * J * (M * M') := by rw [hMM', Matrix.mul_one]
      _ = J * M' := by rw [← Matrix.mul_assoc, hA']
  have h3 : (M'.map fr)ᵀ * J = J * M := by
    calc (M'.map fr)ᵀ * J = (M'.map fr)ᵀ * ((M.map fr)ᵀ * J * M) := by rw [hA']
      _ = (M.map fr * M'.map fr)ᵀ * J * M := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = J * M := by
          rw [← Matrix.map_mul, hMM', Matrix.map_one _ (map_zero fr) (map_one fr), transpose_one,
            Matrix.one_mul]
  have h2 : J * (M'.map fr)ᵀ = M * J := by
    calc J * (M'.map fr)ᵀ = J * ((M'.map fr)ᵀ * J) * J := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = M * J := by rw [h3, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hcomm : (X.map φ).map fr = (X.map fr).map φ := by
    rw [Matrix.map_map, Matrix.map_map]
    ext i j
    simp only [Function.comp_apply, Matrix.map_apply]
    rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, map_pow]
  rw [sigmaSL_eq_stdSL]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_stdSL_conjField, coe_stdSL_graphField, coe_stdSL_graphField, ← map_inv,
    coe_stdSL_conjField, inv_eq_self_of_mul_self revGL_mul_self]
  change (M * (J * (X.map fr)ᵀ * J).map φ * M') i j = (J * ((M * X.map φ * M').map fr)ᵀ * J) i j
  simp only [Matrix.map_mul, transpose_mul, Matrix.transpose_map, hJφ, hcomm]
  simp only [Matrix.mul_assoc]
  rw [h1, ← Matrix.mul_assoc J (M'.map fr)ᵀ, h2]
  simp only [Matrix.mul_assoc]

open YamadaEnd in
theorem exists_extend_msigma {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (θ : msigma F ≃* msigma F) :
    ∃ Θ : MulAut SL(4, F), (∀ x, Θ (sigmaSL F x) = sigmaSL F (Θ x)) ∧
      ∀ A : msigma F, Θ (A : SL(4, F)) = (θ A : SL(4, F)) := by
  have h := unitaryFieldData_of_card_four hF
  have hC : IsPrimeFormGram (revGL 4 F) := isPrimeFormGram_revGL
  obtain ⟨⟨A, φ⟩, hα⟩ := primeFormPsi_surjective h hC (by norm_num) (by norm_num)
    (((msigmaEquivP h).symm.trans θ).trans (msigmaEquivP h))
  rw [primeFormPsi_apply] at hα
  refine ⟨stdSL 4 F A φ 0, stdSL_conjField_sigma h A.2 φ, fun x => ?_⟩
  have hfx : ∀ g : gramSU h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F),
      primeFormFieldHom h hC φ
        (g : primeFormP h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) =
        ((⟨glAut φ (g : GL (Fin 4) F), glAut_mem_gramSU h hC φ g.2⟩ :
          gramSU h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
            primeFormP h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :=
    fun g => primeFormFieldAut_mk h hC φ g
  have h1 : msigmaEquivP h (θ x) =
      (((msigmaEquivP h).symm.trans θ).trans (msigmaEquivP h)) (msigmaEquivP h x) := by
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [← hα, MulAut.mul_apply] at h1
  change ((msigmaToGramSU h (θ x) :
      gramSU h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
        primeFormP h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) =
    primeFormConjHom h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) A
      (primeFormFieldHom h hC φ ((msigmaToGramSU h x :
        gramSU h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
          primeFormP h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))) at h1
  rw [hfx, primeFormConjHom_mk, QuotientGroup.eq, normOneScalars_four_two_eq_bot, Subgroup.mem_bot,
    inv_mul_eq_one] at h1
  have h2 := congrArg (fun g : gramSU h ((revGL 4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =>
    ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h1
  simp only [Units.val_mul, coe_glAut] at h2
  apply Subtype.ext
  rw [coe_stdSL_conjField]
  exact h2.symm

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
