module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUPairBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormSimilitude

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem map_bar_fmap (X : Matrix (Fin n) (Fin n) h.fixedField) :
    (X.map h.fixedField.subtype).map h.bar = X.map h.fixedField.subtype := by
  ext i j
  exact (X i j).2

theorem exists_fmap_of_bar {Y : Matrix (Fin n) (Fin n) K} (hY : Y.map h.bar = Y) :
    ∃ Y' : Matrix (Fin n) (Fin n) h.fixedField, Y'.map h.fixedField.subtype = Y :=
  ⟨Matrix.of fun i j => ⟨Y i j, congrFun (congrFun hY i) j⟩, by ext; rfl⟩

theorem fmap_injective :
    Function.Injective (fun X : Matrix (Fin n) (Fin n) h.fixedField =>
      X.map h.fixedField.subtype) := by
  intro X Y e
  ext i j
  exact congrFun (congrFun e i) j

section Transport

variable (P Pi : Matrix (Fin n) (Fin n) K)

@[expose] def gTr (X : Matrix (Fin n) (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) K :=
  P * X.map h.fixedField.subtype * Pi

variable {P Pi}

theorem gTr_mul (hPiP : Pi * P = 1) (X Y : Matrix (Fin n) (Fin n) h.fixedField) :
    gTr h P Pi (X * Y) = gTr h P Pi X * gTr h P Pi Y := by
  rw [gTr, gTr, gTr, Matrix.map_mul]
  calc P * (X.map h.fixedField.subtype * Y.map h.fixedField.subtype) * Pi =
      P * X.map h.fixedField.subtype * (Pi * P) * Y.map h.fixedField.subtype * Pi := by
        rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem gTr_one (hPPi : P * Pi = 1) : gTr h P Pi 1 = 1 := by
  rw [gTr, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, hPPi]

theorem det_gTr (hPPi : P * Pi = 1) (X : Matrix (Fin n) (Fin n) h.fixedField) :
    (gTr h P Pi X).det = (X.det : K) := by
  have e := congrArg Matrix.det hPPi
  rw [det_mul, det_one] at e
  have e2 := RingHom.map_det h.fixedField.subtype X
  rw [RingHom.mapMatrix_apply] at e2
  rw [gTr, det_mul, det_mul, ← e2]
  change P.det * (X.det : K) * Pi.det = _
  linear_combination (X.det : K) * e

theorem gTr_unitary (hPPi : P * Pi = 1) {s : K} (hs : s ≠ 0)
    {R : Matrix (Fin n) (Fin n) h.fixedField}
    (hR : R.map h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    {X : Matrix (Fin n) (Fin n) h.fixedField} (hX : Xᵀ * R * X = R) :
    ((gTr h P Pi X).map h.bar)ᵀ * gTr h P Pi X = 1 := by
  have hPP : (P.map h.bar)ᵀ * P = s⁻¹ • R.map h.fixedField.subtype := by
    rw [hR, smul_smul, inv_mul_cancel₀ hs, one_smul]
  have hX' : (X.map h.fixedField.subtype)ᵀ * R.map h.fixedField.subtype *
      X.map h.fixedField.subtype = R.map h.fixedField.subtype := by
    rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hX]
  rw [gTr, conjT_mul h, conjT_mul h, map_bar_fmap h]
  calc (Pi.map h.bar)ᵀ * ((X.map h.fixedField.subtype)ᵀ * (P.map h.bar)ᵀ) *
        (P * X.map h.fixedField.subtype * Pi) =
      (Pi.map h.bar)ᵀ * ((X.map h.fixedField.subtype)ᵀ * ((P.map h.bar)ᵀ * P) *
        X.map h.fixedField.subtype) * Pi := by simp only [Matrix.mul_assoc]
    _ = (Pi.map h.bar)ᵀ * ((P.map h.bar)ᵀ * P) * Pi := by
        rw [hPP, Matrix.mul_smul, Matrix.smul_mul, hX', ← hPP]
    _ = ((P * Pi).map h.bar)ᵀ * (P * Pi) := by rw [conjT_mul h]; simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hPPi, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one,
          Matrix.one_mul]

theorem gTr_fixed (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {A : Matrix (Fin n) (Fin n) K}
    {b : K} (hb : b ≠ 0) (hbP : b • (A * P.map h.bar) = P)
    (X : Matrix (Fin n) (Fin n) h.fixedField) :
    A * (gTr h P Pi X).map h.bar = gTr h P Pi X * A := by
  have hPb : P.map h.bar * Pi.map h.bar = 1 := by
    rw [← Matrix.map_mul, hPPi, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  have hAP : A * P.map h.bar = b⁻¹ • P := by
    calc A * P.map h.bar = b⁻¹ • (b • (A * P.map h.bar)) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = b⁻¹ • P := by rw [hbP]
  have hPbi : Pi.map h.bar = b • (Pi * A) := by
    have e1 : (b • (Pi * A)) * P.map h.bar = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_assoc, hAP, Matrix.mul_smul, hPiP, smul_smul,
        mul_inv_cancel₀ hb, one_smul]
    calc Pi.map h.bar = ((b • (Pi * A)) * P.map h.bar) * Pi.map h.bar := by
          rw [e1, Matrix.one_mul]
      _ = b • (Pi * A) := by rw [Matrix.mul_assoc, hPb, Matrix.mul_one]
  rw [gTr, Matrix.map_mul, Matrix.map_mul, map_bar_fmap h, hPbi]
  calc A * (P.map h.bar * X.map h.fixedField.subtype * (b • (Pi * A))) =
      b • ((A * P.map h.bar) * X.map h.fixedField.subtype * Pi * A) := by
        rw [Matrix.mul_smul, Matrix.mul_smul]; simp only [Matrix.mul_assoc]
    _ = P * X.map h.fixedField.subtype * Pi * A := by
        rw [hAP, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, smul_smul,
          mul_inv_cancel₀ hb, one_smul]

theorem exists_similitude_of_scalar (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    {A : Matrix (Fin n) (Fin n) K} {b : K} (hb : b ≠ 0) (hbP : b • (A * P.map h.bar) = P)
    {s : K} (hs : s ≠ 0) {R : Matrix (Fin n) (Fin n) h.fixedField}
    (hR : R.map h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    {H : Matrix (Fin n) (Fin n) K} (hHU : (H.map h.bar)ᵀ * H = 1) {c : K} (hc : h.norm c = 1)
    (hH : A * H.map h.bar = c • (H * A)) :
    ∃ (Y : Matrix (Fin n) (Fin n) h.fixedField) (r : K) (μ : h.fixedField), r ≠ 0 ∧ μ ≠ 0 ∧
      Pi * H * P = r⁻¹ • Y.map h.fixedField.subtype ∧ Yᵀ * R * Y = μ • R := by
  have hPb : P.map h.bar * Pi.map h.bar = 1 := by
    rw [← Matrix.map_mul, hPPi, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  have hAP : A * P.map h.bar = b⁻¹ • P := by
    calc A * P.map h.bar = b⁻¹ • (b • (A * P.map h.bar)) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = b⁻¹ • P := by rw [hbP]
  have hPbi : Pi.map h.bar = b • (Pi * A) := by
    have e1 : (b • (Pi * A)) * P.map h.bar = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_assoc, hAP, Matrix.mul_smul, hPiP, smul_smul,
        mul_inv_cancel₀ hb, one_smul]
    calc Pi.map h.bar = ((b • (Pi * A)) * P.map h.bar) * Pi.map h.bar := by
          rw [e1, Matrix.one_mul]
      _ = b • (Pi * A) := by rw [Matrix.mul_assoc, hPb, Matrix.mul_one]
  set Y₁ := Pi * H * P with hY₁
  have hY₁b : Y₁.map h.bar = c • Y₁ := by
    rw [hY₁, Matrix.map_mul, Matrix.map_mul, hPbi]
    calc b • (Pi * A) * H.map h.bar * P.map h.bar =
        b • (Pi * (A * H.map h.bar) * P.map h.bar) := by
          rw [Matrix.smul_mul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = b • (c • (Pi * H * (A * P.map h.bar))) := by
          rw [hH, Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = c • (Pi * H * P) := by
          rw [hAP, Matrix.mul_smul, smul_comm c, smul_smul, smul_smul, mul_inv_cancel₀ hb,
            one_mul]
  obtain ⟨r, hr0, hr⟩ := h.exists_div_bar_eq hc
  have hbr0 : h.bar r ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hfix : (r • Y₁).map h.bar = r • Y₁ := by
    rw [show (r • Y₁).map h.bar = h.bar r • Y₁.map h.bar by ext i j; simp [map_mul], hY₁b,
      smul_smul, ← hr]
    congr 1
    field_simp
  obtain ⟨Y, hY⟩ := exists_fmap_of_bar h hfix
  have hY₁Y : Y₁ = r⁻¹ • Y.map h.fixedField.subtype := by
    rw [hY, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  have hPP : (P.map h.bar)ᵀ * P = s⁻¹ • R.map h.fixedField.subtype := by
    rw [hR, smul_smul, inv_mul_cancel₀ hs, one_smul]
  have hgram : (Y₁.map h.bar)ᵀ * ((P.map h.bar)ᵀ * P) * Y₁ = (P.map h.bar)ᵀ * P := by
    have hPbT : (Pi.map h.bar)ᵀ * (P.map h.bar)ᵀ = 1 := by
      rw [← transpose_mul, hPb, transpose_one]
    rw [hY₁, conjT_mul h, conjT_mul h]
    calc (P.map h.bar)ᵀ * ((H.map h.bar)ᵀ * (Pi.map h.bar)ᵀ) * ((P.map h.bar)ᵀ * P) *
          (Pi * H * P) =
        (P.map h.bar)ᵀ * (H.map h.bar)ᵀ * ((Pi.map h.bar)ᵀ * (P.map h.bar)ᵀ) * (P * Pi) *
          H * P := by simp only [Matrix.mul_assoc]
      _ = (P.map h.bar)ᵀ * P := by
          rw [hPbT, hPPi, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc _ _ H, hHU,
            Matrix.mul_one]
  have hNr : h.norm r ∈ h.fixedField := h.norm_mem_fixedField r
  set μ : h.fixedField := ⟨h.norm r, hNr⟩ with hμ
  have hμ0 : μ ≠ 0 := by
    intro e
    have := congrArg Subtype.val e
    simp only [hμ, ZeroMemClass.coe_zero] at this
    rw [UnitaryFieldData.norm] at this
    exact mul_ne_zero hr0 hbr0 this
  refine ⟨Y, r, μ, hr0, hμ0, hY₁Y, (fmap_injective h) ?_⟩
  simp only [Matrix.map_mul, transpose_map, Matrix.map_smul' _ _ _ (map_mul _)]
  rw [hY₁Y, hPP] at hgram
  have hYb : (r⁻¹ • Y.map h.fixedField.subtype).map h.bar =
      (h.bar r)⁻¹ • Y.map h.fixedField.subtype := by
    rw [show (r⁻¹ • Y.map h.fixedField.subtype).map h.bar =
      h.bar r⁻¹ • (Y.map h.fixedField.subtype).map h.bar by ext i j; simp [map_mul],
      map_bar_fmap h, map_inv₀]
  rw [hYb] at hgram
  simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at hgram
  have e := congrArg (fun M => (h.bar r * r * s) • M) hgram
  simp only [smul_smul] at e
  rw [show h.bar r * r * s * (r⁻¹ * (s⁻¹ * (h.bar r)⁻¹)) = 1 by field_simp, one_smul,
    show h.bar r * r * s * s⁻¹ = h.bar r * r by field_simp] at e
  rw [e]
  congr 1
  simp only [hμ, Subfield.subtype_apply, UnitaryFieldData.norm]
  ring

end Transport

section Similitude

variable {F : Type} [Field F]

theorem conj_mem_isometryGroup_of_similitude {R Y X : GL (Fin n) F} {μ : F}
    (hY : (Y : Matrix (Fin n) (Fin n) F)ᵀ * R * Y = μ • (R : Matrix (Fin n) (Fin n) F))
    (hμ : μ ≠ 0) (hX : X ∈ CatalogueBGraphForm.isometryGroup n F R) :
    Y * X * Y⁻¹ ∈ CatalogueBGraphForm.isometryGroup n F R := by
  rw [CatalogueBGraphForm.mem_isometryGroup] at hX ⊢
  have hYi : (Y : Matrix (Fin n) (Fin n) F) * ((Y⁻¹ : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hYiT : ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *
      (Y : Matrix (Fin n) (Fin n) F)ᵀ = 1 := by rw [← transpose_mul, hYi, transpose_one]
  have hR' : ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * R *
      ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = μ⁻¹ • (R : Matrix (Fin n) (Fin n) F) := by
    have e : μ • (((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * R *
        ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = R := by
      calc μ • (((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * R *
            ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
          ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *
            (μ • (R : Matrix (Fin n) (Fin n) F)) *
            ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
            rw [Matrix.mul_smul, Matrix.smul_mul]
        _ = ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * (Y : Matrix (Fin n) (Fin n) F)ᵀ *
            R * (Y * ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
            rw [← hY]; simp only [Matrix.mul_assoc]
        _ = R := by rw [hYiT, hYi, Matrix.one_mul, Matrix.mul_one]
    calc ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * R *
          ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        μ⁻¹ • (μ • (((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * R *
          ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))) := by
          rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • (R : Matrix (Fin n) (Fin n) F) := by rw [e]
  rw [Units.val_mul, Units.val_mul, transpose_mul, transpose_mul]
  calc ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * ((X : Matrix (Fin n) (Fin n) F)ᵀ *
        (Y : Matrix (Fin n) (Fin n) F)ᵀ) * R *
        (Y * X * ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * ((X : Matrix (Fin n) (Fin n) F)ᵀ *
        ((Y : Matrix (Fin n) (Fin n) F)ᵀ * R * Y) * X) *
        ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by simp only [Matrix.mul_assoc]
    _ = μ • (((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * R *
        ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
        rw [hY, Matrix.mul_smul, Matrix.smul_mul, hX, Matrix.mul_smul, Matrix.smul_mul]
    _ = R := by rw [hR', smul_smul, mul_inv_cancel₀ hμ, one_smul]

theorem conj_mem_commutator_isometryGroup_of_similitude {R Y X : GL (Fin n) F} {μ : F}
    (hY : (Y : Matrix (Fin n) (Fin n) F)ᵀ * R * Y = μ • (R : Matrix (Fin n) (Fin n) F))
    (hμ : μ ≠ 0) (hX : X ∈ ⁅CatalogueBGraphForm.isometryGroup n F R,
      CatalogueBGraphForm.isometryGroup n F R⁆) :
    Y * X * Y⁻¹ ∈ ⁅CatalogueBGraphForm.isometryGroup n F R,
      CatalogueBGraphForm.isometryGroup n F R⁆ := by
  set I := CatalogueBGraphForm.isometryGroup n F R
  have hle : I.map (MulAut.conj Y).toMonoidHom ≤ I := by
    rintro _ ⟨Z, hZ, rfl⟩
    exact conj_mem_isometryGroup_of_similitude hY hμ hZ
  have h1 : (⁅I, I⁆).map (MulAut.conj Y).toMonoidHom ≤ ⁅I, I⁆ := by
    rw [map_commutator]
    exact commutator_mono hle hle
  exact h1 ⟨X, hX, rfl⟩

end Similitude

end CFSG.ComponentClassification.Burgoyne.U
