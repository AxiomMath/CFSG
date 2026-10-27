module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAProj
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpL4

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.PSpL
  CFSG.ComponentClassification.CatFactsL4U4.StabL CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsSp4
open CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

section Mult

theorem ka_gsp_mult_pow {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]
    {g K : Matrix n n F} {c : F} (h : gᵀ * K * g = c • K) (k : ℕ) :
    (g ^ k)ᵀ * K * g ^ k = c ^ k • K := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, one_smul]
  | succ k ih =>
    rw [pow_succ, Matrix.transpose_mul, pow_succ c k]
    calc gᵀ * (g ^ k)ᵀ * K * (g ^ k * g) = gᵀ * ((g ^ k)ᵀ * K * g ^ k) * g := by
          simp only [Matrix.mul_assoc]
      _ = (c ^ k * c) • K := by
          rw [ih, Matrix.mul_smul, Matrix.smul_mul, h, smul_smul]

theorem ka_gsp_mult_scalar {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]
    (K : Matrix n n F) (z : F) :
    ((z • 1 : Matrix n n F))ᵀ * K * (z • 1 : Matrix n n F) = (z * z) • K := by
  simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul]

theorem ka_gsp_sq_eq_one {F : Type*} [Field F] {c z : F} {m : ℕ} (hm : Odd m) (hc4 : c ^ 4 = 1)
    (hz4 : z ^ 4 = 1) (h : c ^ m = z ^ 2) : c ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have h1 : (c ^ (2 * k + 1)) ^ 2 = 1 := by
    rw [h, ← pow_mul]
    exact hz4
  calc c ^ 2 = (c ^ 4) ^ k * c ^ 2 := by rw [hc4, one_pow, one_mul]
    _ = (c ^ (2 * k + 1)) ^ 2 := by
        rw [← pow_mul, ← pow_add, ← pow_mul]
        congr 1
        ring
    _ = 1 := h1

end Mult

theorem ka_gsp_mult_of_fix {F : Type} [Field F] (A : GL (Fin 4) F) (g : SL(4, F))
    (hy : (conjAut 4 F A * dualAut 4 F) (proj 4 F g) = proj 4 F g) :
    ∃ c : Fˣ, c ^ 4 = 1 ∧
      (g : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (g : Matrix (Fin 4) (Fin 4) F) =
        (c : F) • ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj] at hy
  obtain ⟨c, hc4, hc⟩ := mem_scalars.1 (proj_eq_proj_iff.1 hy)
  refine ⟨c, hc4, ?_⟩
  set S := CatalogueBHigherLinearAction.slConjugation 4 F A (g⁻¹).transpose with hS
  set h : Matrix (Fin 4) (Fin 4) F := ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) with hh
  set Ai : Matrix (Fin 4) (Fin 4) F := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    with hAi
  have hSmat : (S : Matrix (Fin 4) (Fin 4) F) = (A : Matrix (Fin 4) (Fin 4) F) * hᵀ * Ai := by
    rw [hS, coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
  have hscal : (Matrix.scalar (Fin 4) (c : F) : Matrix (Fin 4) (Fin 4) F) = (c : F) • 1 := by
    rw [smul_one_eq_diagonal]
    rfl
  have hg : (g : Matrix (Fin 4) (Fin 4) F) =
      (c : F) • ((A : Matrix (Fin 4) (Fin 4) F) * hᵀ * Ai) := by
    calc (g : Matrix (Fin 4) (Fin 4) F) = ((S * (S⁻¹ * g) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) :=
          congrArg Subtype.val (mul_inv_cancel_left S g).symm
      _ = (S : Matrix (Fin 4) (Fin 4) F) * ((S⁻¹ * g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) :=
          Matrix.SpecialLinearGroup.coe_mul _ _
      _ = _ := by rw [hc, hscal, hSmat, Matrix.mul_smul, Matrix.mul_one]
  have hhg : h * (g : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hh, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hAiA : Ai * (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAig : Ai * (g : Matrix (Fin 4) (Fin 4) F) = (c : F) • (hᵀ * Ai) := by
    rw [hg, Matrix.mul_smul]
    congr 1
    calc Ai * ((A : Matrix (Fin 4) (Fin 4) F) * hᵀ * Ai) = (Ai * A) * hᵀ * Ai := by
          simp only [Matrix.mul_assoc]
      _ = hᵀ * Ai := by rw [hAiA, Matrix.one_mul]
  calc (g : Matrix (Fin 4) (Fin 4) F)ᵀ * Ai * (g : Matrix (Fin 4) (Fin 4) F)
      = (g : Matrix (Fin 4) (Fin 4) F)ᵀ * (Ai * (g : Matrix (Fin 4) (Fin 4) F)) := by
        rw [Matrix.mul_assoc]
    _ = (c : F) • ((g : Matrix (Fin 4) (Fin 4) F)ᵀ * hᵀ * Ai) := by
        rw [hAig, Matrix.mul_smul, Matrix.mul_assoc]
    _ = (c : F) • Ai := by
        rw [← Matrix.transpose_mul, hhg, Matrix.transpose_one, Matrix.one_mul]

section Frame

variable {F : Type} [Field F]

@[expose] noncomputable def kaGspEmb (P : GL (Fin 4) F) : StatedSp 2 F →* SL(4, F) where
  toFun M := ⟨((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F), by
    have hPP : (P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, det_mul, det_mul,
      (spGL_spec F M).2, mul_one, ← det_mul, hPP, det_one]⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one, Units.val_one, Matrix.SpecialLinearGroup.coe_one]
  map_mul' M N := by
    apply Subtype.ext
    show ((MulAut.conj P (spGL F (M * N)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((MulAut.conj P (spGL F N) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [map_mul, map_mul, Units.val_mul]

theorem coe_kaGspEmb (P : GL (Fin 4) F) (M : StatedSp 2 F) :
    ((kaGspEmb P M : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * ((spGL F M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) := by
  change ((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul]

variable {K : Matrix (Fin 4) (Fin 4) F}

theorem kaGspEmb_symp {P : GL (Fin 4) F}
    (hP : (P : Matrix (Fin 4) (Fin 4) F)ᵀ * K * (P : Matrix (Fin 4) (Fin 4) F) = omg)
    (M : StatedSp 2 F) :
    ((kaGspEmb P M : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ * K *
      ((kaGspEmb P M : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = K := by
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [coe_kaGspEmb]
  apply conj_transpose_mul_mul hPP
  rw [hP]
  exact (spGL_spec F M).1

theorem kaGspEmb_surj {P : GL (Fin 4) F}
    (hP : (P : Matrix (Fin 4) (Fin 4) F)ᵀ * K * (P : Matrix (Fin 4) (Fin 4) F) = omg)
    (g : SL(4, F))
    (hg : (g : Matrix (Fin 4) (Fin 4) F)ᵀ * K * (g : Matrix (Fin 4) (Fin 4) F) = K) :
    ∃ M : StatedSp 2 F, kaGspEmb P M = g := by
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F) with hPm
  set Pi : Matrix (Fin 4) (Fin 4) F := (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) with hPi
  have hPP : Pm * Pi = 1 := by
    rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by
    rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hK : Piᵀ * omg * Pi = K := by
    rw [← hP]
    calc Piᵀ * (Pmᵀ * K * Pm) * Pi = (Pm * Pi)ᵀ * K * (Pm * Pi) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = K := by rw [hPP, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hX : (Pi * (g : Matrix (Fin 4) (Fin 4) F) * Pm)ᵀ * omg *
      (Pi * (g : Matrix (Fin 4) (Fin 4) F) * Pm) = omg := by
    apply conj_transpose_mul_mul hPiP
    rw [hK]
    exact hg
  set X : Matrix (Fin 4) (Fin 4) F := Pi * (g : Matrix (Fin 4) (Fin 4) F) * Pm with hXdef
  set e := Matrix.reindexAlgEquiv F F (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin (2 + 2)) with he
  set M₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := e.symm X with hM₀
  have heM₀ : e M₀ = X := e.apply_symm_apply X
  have hsymp : M₀ᵀ * SymplecticHigher.formJ 2 F * M₀ = SymplecticHigher.formJ 2 F := by
    apply e.injective
    rw [map_mul, map_mul, heM₀]
    have h1 : e (M₀ᵀ) = (e M₀)ᵀ := by
      rw [he, Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex]
    have h2 : e (SymplecticHigher.formJ 2 F) = omg := by
      rw [he, Matrix.coe_reindexAlgEquiv]
      exact reindex_gram
    rw [h1, heM₀, h2]
    exact hX
  refine ⟨toSp M₀ hsymp, ?_⟩
  apply Subtype.ext
  rw [coe_kaGspEmb]
  have h3 : ((spGL F (toSp M₀ hsymp) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = X := by
    rw [coe_spGL]
    exact heM₀
  rw [h3, hXdef]
  calc Pm * (Pi * (g : Matrix (Fin 4) (Fin 4) F) * Pm) * Pi
      = (Pm * Pi) * (g : Matrix (Fin 4) (Fin 4) F) * (Pm * Pi) := by
        simp only [Matrix.mul_assoc]
    _ = (g : Matrix (Fin 4) (Fin 4) F) := by rw [hPP, Matrix.one_mul, Matrix.mul_one]

end Frame

section Root

variable {F : Type} [Field F]

@[expose] def kaGspNil : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks 0 1 0 0

theorem kaGspNil_ne_zero : (kaGspNil : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ 0 := by
  intro h
  have := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
  simp only [kaGspNil, Fin.isValue, Matrix.fromBlocks_apply₁₂, Matrix.one_apply_eq,
    Matrix.zero_apply, one_ne_zero] at this

theorem kaGspNil_mul_self :
    (kaGspNil : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * kaGspNil = 0 := by
  rw [kaGspNil, fromBlocks_multiply]
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_one, Matrix.fromBlocks_zero]

theorem kaGspNil_symp (c : F) :
    (1 + c • kaGspNil : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * SymplecticHigher.formJ 2 F *
      (1 + c • kaGspNil) = SymplecticHigher.formJ 2 F := by
  have h1 : (1 + c • kaGspNil : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks 1 (c • 1) 0 1 := by
    rw [kaGspNil, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
    simp only [smul_zero, add_zero, zero_add]
  rw [h1, SymplecticHigher.formJ, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.transpose_one, Matrix.mul_zero, Matrix.transpose_zero, Matrix.mul_neg,
    Matrix.mul_one, neg_zero, add_zero, Matrix.mul_smul, smul_zero, zero_add,
    Matrix.transpose_smul, smul_neg, neg_add_cancel]

end Root

section Odd

variable {F : Type} [Field F]

theorem ka_gsp_odd_mem_range (A P : GL (Fin 4) F)
    (hP : (P : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (P : Matrix (Fin 4) (Fin 4) F) = omg) {y : projectiveSL 4 F}
    (hy : (conjAut 4 F A * dualAut 4 F) y = y) (hodd : Odd (orderOf y)) :
    y ∈ ((proj 4 F).comp (kaGspEmb P)).range := by
  obtain ⟨g, rfl⟩ := proj_surjective 4 F y
  obtain ⟨c, hc4, hc⟩ := ka_gsp_mult_of_fix A g hy
  set K : Matrix (Fin 4) (Fin 4) F := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hK
  have hKA : K * (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hK, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcancel : ∀ a b : F, a • K = b • K → a = b := by
    intro a b hab
    have h := congrArg (fun M => M * (A : Matrix (Fin 4) (Fin 4) F)) hab
    simp only [Matrix.smul_mul, hKA] at h
    have := congrFun (congrFun h 0) 0
    simpa only [Fin.isValue, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using
      this
  have hscal : ∀ u : F, (Matrix.scalar (Fin 4) u : Matrix (Fin 4) (Fin 4) F) = u • 1 := by
    intro u
    rw [smul_one_eq_diagonal]
    rfl
  have hgm : g ^ orderOf (proj 4 F g) ∈ scalars 4 F := by
    rw [← proj_eq_one_iff, map_pow]
    exact pow_orderOf_eq_one _
  obtain ⟨z, hz4, hz⟩ := mem_scalars.1 hgm
  have hgz : (g : Matrix (Fin 4) (Fin 4) F) ^ orderOf (proj 4 F g) = (z : F) • 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hz, hscal]
  have h1 := ka_gsp_mult_pow hc (orderOf (proj 4 F g))
  rw [hgz, ka_gsp_mult_scalar] at h1
  have h2 : (c : F) ^ orderOf (proj 4 F g) = (z : F) * z := (hcancel _ _ h1).symm
  have hc4' : (c : F) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]
  have hz4' : (z : F) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hz4, Units.val_one]
  have hcc : (c : F) ^ 2 = 1 := ka_gsp_sq_eq_one hodd hc4' hz4' (by rw [h2, sq])
  have hcc' : (c : F) * c = 1 := by rw [← sq]; exact hcc
  rcases mul_self_eq_one_iff.1 hcc' with hc1 | hc1
  · obtain ⟨M, hM⟩ := kaGspEmb_surj hP g (by rw [hc, hc1, one_smul])
    exact ⟨M, by rw [MonoidHom.comp_apply, hM]⟩
  · have hzz : (z : F) * z = -1 := by rw [← h2, hc1]; exact hodd.neg_one_pow
    set w : F := ((z⁻¹ : Fˣ) : F) with hw
    have hwz : w * (z : F) = 1 := Units.inv_mul z
    have hww : w * w = -1 := by
      have h3 : (w * w) * ((z : F) * z) = 1 := by
        calc (w * w) * ((z : F) * z) = (w * z) * (w * z) := by ring
          _ = 1 := by rw [hwz, one_mul]
      rw [hzz] at h3
      linear_combination -h3
    have hdet : (w • (g : Matrix (Fin 4) (Fin 4) F)).det = 1 := by
      rw [Matrix.det_smul, g.2, mul_one, Fintype.card_fin]
      calc w ^ 4 = (w * w) * (w * w) := by ring
        _ = 1 := by rw [hww, neg_mul_neg, mul_one]
    set g' : SL(4, F) := ⟨w • (g : Matrix (Fin 4) (Fin 4) F), hdet⟩ with hg'
    have hg'symp :
        (g' : Matrix (Fin 4) (Fin 4) F)ᵀ * K * (g' : Matrix (Fin 4) (Fin 4) F) = K := by
      change (w • (g : Matrix (Fin 4) (Fin 4) F))ᵀ * K * (w • (g : Matrix (Fin 4) (Fin 4) F)) = K
      simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [hc, hc1, smul_smul, hww]
      simp only [mul_neg, mul_one, neg_neg, one_smul]
    have hs : (g' * scalarElement z hz4 : SL(4, F)) = g := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, hscal]
      change (w • (g : Matrix (Fin 4) (Fin 4) F)) * ((z : F) • 1) = g
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hwz, one_smul]
    have hproj : proj 4 F g' = proj 4 F g := by
      conv_rhs => rw [← hs]
      rw [map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars z hz4), mul_one]
    obtain ⟨M, hM⟩ := kaGspEmb_surj hP g' hg'symp
    exact ⟨M, by rw [MonoidHom.comp_apply, hM, hproj]⟩

end Odd

section Darboux

variable {F : Type} [Field F]

theorem ka_gsp_darboux (h2 : (2 : F) ≠ 0) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    ∃ P : GL (Fin 4) F, (P : Matrix (Fin 4) (Fin 4) F)ᵀ *
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = omg := by
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
  exact exists_transpose_mul_mul_eq_omg h2 hRt hRu

theorem ka_gsp_scalar_sq {z : StatedSp 2 F} (hz : z ∈ SymplecticHigher.spScalars 2 F) :
    z * z = 1 := by
  apply sp_ext
  rcases (mem_spScalars_iff z).mp hz with h | h
  · simp only [Subgroup.coe_mul, Units.val_mul, h, Matrix.mul_one, OneMemClass.coe_one,
      Units.val_one]
  · simp only [Subgroup.coe_mul, Units.val_mul, h, Matrix.mul_neg, Matrix.mul_one, neg_neg,
      OneMemClass.coe_one, Units.val_one]

theorem ka_gsp_hRp {Y : Type} [Group Y] [Finite Y] (ϖ : StatedSp 2 F →* Y)
    (hQ : CFSG.IsQuasisimple (StatedSp 2 F)) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup Y, IsPGroup p ↥X → X ≤ ϖ.range →
      (∀ r ∈ ϖ.range, r ∈ normalizer (X : Set Y)) → X = ⊥ := by
  intro p hp hp2 X hXp hXR hXn
  let N : Subgroup (StatedSp 2 F) := X.comap ϖ
  have hNn : N.Normal := ⟨fun n hn g => by
    show ϖ (g * n * g⁻¹) ∈ X
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hXn (ϖ g) ⟨g, rfl⟩) (ϖ n)).1 hn⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ N with hN | hN
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨m, rfl⟩ := hXR hx
    have hm : m ∈ Subgroup.center (StatedSp 2 F) := hN hx
    rw [CFSG.LieType.Universal.Symplectic.center_eq] at hm
    have hmm : ϖ m * ϖ m ∈ (⊥ : Subgroup Y) := by
      rw [← map_mul, ka_gsp_scalar_sq hm, map_one]
      exact Subgroup.one_mem _
    exact ka_odd_mem_of_sq_mem hmm (ka_odd_of_mem_pGroup hp hp2 hXp hx)
  · have hRX : ϖ.range ≤ X := by
      rintro _ ⟨e, rfl⟩
      have : e ∈ N := hN ▸ Subgroup.mem_top e
      exact this
    have hXeq : X = ϖ.range := le_antisymm hXR hRX
    have : Group.IsPerfect (StatedSp 2 F) := hQ.1
    have : Fact p.Prime := ⟨hp⟩
    subst hXeq
    have : Group.IsPerfect ↥ϖ.range := Group.IsPerfect.range ϖ
    have hnil : Group.IsNilpotent ↥ϖ.range := hXp.isNilpotent
    by_contra hne
    have : Nontrivial ↥ϖ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isNilpotent ↥ϖ.range hnil

theorem ka_gsp_rigid [Finite F] (hodd : ringChar F ≠ 2) (P : GL (Fin 4) F) :
    KARigid ((proj 4 F).comp (kaGspEmb P)).range := by
  set e := Matrix.reindexAlgEquiv F F (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin (2 + 2)) with he
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F) with hPm
  set Pi : Matrix (Fin 4) (Fin 4) F := (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) with hPi
  have hPP : Pm * Pi = 1 := by
    rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by
    rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set N : Matrix (Fin 4) (Fin 4) F := Pm * e kaGspNil * Pi with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply kaGspNil_ne_zero (F := F)
    apply e.injective
    rw [map_zero]
    calc e kaGspNil = (Pi * Pm) * e kaGspNil * (Pi * Pm) := by
          rw [hPiP, Matrix.one_mul, Matrix.mul_one]
      _ = Pi * N * Pm := by rw [hN]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  have hN2 : N * N = 0 := by
    calc N * N = Pm * (e kaGspNil * ((Pi * Pm) * e kaGspNil)) * Pi := by
          rw [hN]; simp only [Matrix.mul_assoc]
      _ = Pm * (e (kaGspNil * kaGspNil)) * Pi := by rw [hPiP, Matrix.one_mul, map_mul]
      _ = 0 := by rw [kaGspNil_mul_self, map_zero, Matrix.mul_zero, Matrix.zero_mul]
  refine ka_rigid_proj (n := 4) (F := F) (by norm_num)
    (fun A hA => ka_conjAut_inner_of_odd_pl4 hodd A hA) _ N hN0 hN2 ?_
  intro c
  refine ⟨kaGspEmb P (toSp _ (kaGspNil_symp c)), ?_, ⟨_, rfl⟩⟩
  rw [coe_kaGspEmb, coe_spGL]
  change Pm * e (1 + c • kaGspNil) * Pi = 1 + c • N
  rw [map_add, map_one, map_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP,
    Matrix.mul_smul, Matrix.smul_mul]

end Darboux

theorem kaL4GSp_thm : KAL4GSp := by
  intro F _ _ hodd A hA
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  obtain ⟨P, hP⟩ := ka_gsp_darboux h2 A hA
  have hfix : ∀ M, (conjAut 4 F A * dualAut 4 F) (((proj 4 F).comp (kaGspEmb P)) M) =
      ((proj 4 F).comp (kaGspEmb P)) M := fun M => by
    rw [MonoidHom.comp_apply]
    exact conjAut_dualAut_proj_of_transpose_mul_mul A _ (kaGspEmb_symp hP M)
  have hFodd : Odd (Nat.card F) := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hodd)
  have hc35 : Nat.card F = 3 ∨ 5 ≤ Nat.card F := by
    have hlt := Finite.one_lt_card (α := F)
    obtain ⟨k, hk⟩ := hFodd
    omega
  have hQ : CFSG.IsQuasisimple (StatedSp 2 F) := by
    refine CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num) ?_
    rcases hc35 with h3 | h5
    · exact Or.inr (Or.inl ⟨h3, le_refl 2⟩)
    · exact Or.inl (Or.inr (by omega))
  have hperf : Group.IsPerfect ↥((proj 4 F).comp (kaGspEmb P)).range :=
    have : Group.IsPerfect (StatedSp 2 F) := hQ.1
    Group.IsPerfect.range _
  refine ka_all_of_rigid (ka_conj_inj_pl4 hodd) ((proj 4 F).comp (kaGspEmb P)).range ?_
    (Subgroup.isPerfect_iff.mp hperf) ?_ (ka_gsp_hRp _ hQ) (ka_gsp_rigid hodd P)
  · rintro _ ⟨M, rfl⟩
    exact mem_fixSub.2 (hfix M)
  · intro c hc ho
    exact ka_gsp_odd_mem_range A P hP (mem_fixSub.1 hc) ho

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
