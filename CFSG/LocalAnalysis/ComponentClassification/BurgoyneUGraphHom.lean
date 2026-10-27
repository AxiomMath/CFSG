module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUElem

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

abbrev iso1 (R : GL (Fin n) h.fixedField) : Subgroup (GL (Fin n) h.fixedField) :=
  CatalogueBGraphForm.isometryGroup n h.fixedField R ⊓
    (Matrix.GeneralLinearGroup.det : GL (Fin n) h.fixedField →* h.fixedFieldˣ).ker

theorem det_of_mem_iso1 {R X : GL (Fin n) h.fixedField} (hX : X ∈ iso1 h R) :
    (X : Matrix (Fin n) (Fin n) h.fixedField).det = 1 := by
  have h1 : X ∈ (Matrix.GeneralLinearGroup.det : GL (Fin n) h.fixedField →*
      h.fixedFieldˣ).ker := (Subgroup.mem_inf.1 hX).2
  rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply,
    Units.val_one] at h1
  exact h1

section Hom

variable {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {s : K}
  (hs : s ≠ 0) {R : GL (Fin n) h.fixedField}
  (hR : (R : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype =
    s • ((P.map h.bar)ᵀ * P))

@[expose] def gHom : iso1 h R →* StatedSU n (p ^ f) K where
  toFun X := uSUmk h (gTr h P Pi ((X : GL (Fin n) h.fixedField) :
      Matrix (Fin n) (Fin n) h.fixedField))
    (by rw [det_gTr h hPPi, det_of_mem_iso1 h X.2]; rfl)
    (gTr_unitary h hPPi hs hR ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 X.2.1))
  map_one' := Subtype.ext (Units.ext (by
    change gTr h P Pi ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) = 1
    rw [Units.val_one, gTr_one h hPPi]))
  map_mul' X Y := Subtype.ext (Units.ext (by
    change gTr h P Pi (((X * Y : iso1 h R) : GL (Fin n) h.fixedField) :
      Matrix (Fin n) (Fin n) h.fixedField) = gTr h P Pi _ * gTr h P Pi _
    rw [Subgroup.coe_mul, Units.val_mul, gTr_mul h hPiP]))

theorem coe_gHom (X : iso1 h R) :
    (((gHom h hPPi hPiP hs hR X : StatedSU n (p ^ f) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      gTr h P Pi ((X : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) := rfl

theorem gHom_injective : Function.Injective (gHom h hPPi hPiP hs hR) := by
  intro X Y e
  have e1 := congrArg (fun g : StatedSU n (p ^ f) K =>
    Pi * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P) e
  simp only [coe_gHom, gTr] at e1
  have key : ∀ Z : Matrix (Fin n) (Fin n) h.fixedField,
      Pi * (P * Z.map h.fixedField.subtype * Pi) * P = Z.map h.fixedField.subtype := by
    intro Z
    calc Pi * (P * Z.map h.fixedField.subtype * Pi) * P =
        (Pi * P) * Z.map h.fixedField.subtype * (Pi * P) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPiP, Matrix.one_mul, Matrix.mul_one]
  rw [key, key] at e1
  exact Subtype.ext (Units.ext (fmap_injective h e1))

theorem uLift_gHom {A : uU h n} {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    (X : iso1 h R) :
    uLift h A (barEq h) (gHom h hPPi hPiP hs hR X) = gHom h hPPi hPiP hs hR X := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_uLift, coe_gHom]
  have e := gTr_fixed h hPPi hPiP hb hbP
    ((X : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField)
  have hAi : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  change ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (gTr h P Pi ((X : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField)).map
        h.bar *
      (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
  rw [e, Matrix.mul_assoc, hAi, Matrix.mul_one]

theorem conj_mem_map_gHom (hn : 1 ≤ n) {A : uU h n} {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {Ω : Subgroup (GL (Fin n) h.fixedField)} (hΩ1 : Ω ≤ iso1 h R)
    (hΩ : ∀ (Y : GL (Fin n) h.fixedField) (μ : h.fixedField), μ ≠ 0 →
      (Y : Matrix (Fin n) (Fin n) h.fixedField)ᵀ * R * Y =
        μ • (R : Matrix (Fin n) (Fin n) h.fixedField) → ∀ X ∈ Ω, Y * X * Y⁻¹ ∈ Ω)
    {H : StatedSU n (p ^ f) K}
    (hH : H⁻¹ * uLift h A (barEq h) H ∈
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))
    {g : StatedSU n (p ^ f) K}
    (hg : g ∈ (Ω.subgroupOf (iso1 h R)).map (gHom h hPPi hPiP hs hR)) :
    H * g * H⁻¹ ∈ (Ω.subgroupOf (iso1 h R)).map (gHom h hPPi hPiP hs hR) := by
  obtain ⟨X, hX, rfl⟩ := hg
  obtain ⟨c, hc⟩ := hH
  have hc0 : ((H⁻¹ * uLift h A (barEq h) H : StatedSU n (p ^ f) K) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c := hc.symm
  set Hm := ((H : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hHm
  set Hi := (((H⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hHi
  have hHHi : Hm * Hi = 1 := by
    rw [hHm, hHi, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one]
  have hHiH : Hi * Hm = 1 := mul_eq_one_comm.1 hHHi
  have hHU : (Hm.map h.bar)ᵀ * Hm = 1 := ((mem_unitarySU_iff h).1 H.2).2
  have hφ : (((uLift h A (barEq h) H : StatedSU n (p ^ f) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (c : K) • Hm := by
    have e : uLift h A (barEq h) H = H * (H⁻¹ * uLift h A (barEq h) H) := by
      rw [mul_inv_cancel_left]
    rw [e, Subgroup.coe_mul, Units.val_mul]
    have hc' : (((H⁻¹ * uLift h A (barEq h) H : StatedSU n (p ^ f) K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (c : K) • 1 := by
      rw [hc0, GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
      rfl
    rw [hc', Matrix.mul_smul, Matrix.mul_one]
  have hcN : h.norm (c : K) = 1 := by
    have hz := ((mem_unitarySU_iff h).1 (H⁻¹ * uLift h A (barEq h) H).2).2
    rw [hc0, GeneralLinearGroup.coe_scalar] at hz
    have e := congrFun (congrFun hz ⟨0, hn⟩) ⟨0, hn⟩
    simp only [Matrix.mul_apply, transpose_apply, map_apply, Matrix.scalar_apply,
      diagonal_apply, one_apply_eq] at e
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n) (fun k _ hk => by simp [hk])
      (by simp)] at e
    simp only [↓reduceIte] at e
    rw [UnitaryFieldData.norm, mul_comm]
    exact e
  have hAH : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Hm.map h.bar =
      (c : K) • (Hm * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have e := hφ
    rw [coe_uLift] at e
    have hAiA : (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Hm.map h.bar =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Hm.map h.bar *
          ((((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hAiA, Matrix.mul_one]
      _ = (c : K) • (Hm * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [← Matrix.mul_assoc]
          change ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (((H : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (barEq h)) *
            (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
          rw [e, Matrix.smul_mul]
  obtain ⟨Y, r, μ, hr0, hμ0, hY, hYR⟩ := exists_similitude_of_scalar h hPPi hPiP hb hbP hs hR
    hHU hcN hAH
  have hYdet : Y.det ≠ 0 := by
    have e := congrArg Matrix.det hYR
    rw [det_mul, det_mul, det_transpose, det_smul, Fintype.card_fin] at e
    have hR0 : (R : Matrix (Fin n) (Fin n) h.fixedField).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 R.isUnit).ne_zero
    intro h0
    rw [h0, zero_mul, zero_mul] at e
    exact mul_ne_zero (pow_ne_zero n hμ0) hR0 e.symm
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.2 hYdet
  set YG : GL (Fin n) h.fixedField := ⟨Y, Y⁻¹, Matrix.mul_nonsing_inv Y hYu,
    Matrix.nonsing_inv_mul Y hYu⟩ with hYG
  have hX' : YG * (X : GL (Fin n) h.fixedField) * YG⁻¹ ∈ Ω := hΩ YG μ hμ0 hYR _ hX
  refine ⟨⟨YG * (X : GL (Fin n) h.fixedField) * YG⁻¹, hΩ1 hX'⟩, hX', Subtype.ext (Units.ext ?_)⟩
  have hHm' : Hm = P * (r⁻¹ • Y.map h.fixedField.subtype) * Pi := by
    rw [← hY]
    calc Hm = (P * Pi) * Hm * (P * Pi) := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hYY : Y.map h.fixedField.subtype * (Y⁻¹).map h.fixedField.subtype = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv Y hYu,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hsc : ∀ M N : Matrix (Fin n) (Fin n) K, (r⁻¹ • M) * (r • N) = M * N := by
    intro M N
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  have hHi' : Hi = P * (r • (Y⁻¹).map h.fixedField.subtype) * Pi := by
    have e1 : Hm * (P * (r • (Y⁻¹).map h.fixedField.subtype) * Pi) = 1 := by
      rw [hHm']
      calc P * (r⁻¹ • Y.map h.fixedField.subtype) * Pi *
            (P * (r • (Y⁻¹).map h.fixedField.subtype) * Pi) =
          P * ((r⁻¹ • Y.map h.fixedField.subtype) * (Pi * P) *
            (r • (Y⁻¹).map h.fixedField.subtype)) * Pi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hPiP, Matrix.mul_one, hsc, hYY, Matrix.mul_one, hPPi]
    calc Hi = (Hi * Hm) * (P * (r • (Y⁻¹).map h.fixedField.subtype) * Pi) := by
          rw [Matrix.mul_assoc, e1, Matrix.mul_one]
      _ = _ := by rw [hHiH, Matrix.one_mul]
  rw [coe_gHom]
  change gTr h P Pi (Y * ((X : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) *
    Y⁻¹) = Hm * gTr h P Pi ((X : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) *
      Hi
  rw [hHm', hHi', gTr, gTr, Matrix.map_mul, Matrix.map_mul]
  have hPiP' : ∀ M : Matrix (Fin n) (Fin n) K, Pi * (P * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hPiP', Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ hr0, one_smul]

end Hom

end CFSG.ComponentClassification.Burgoyne.U
