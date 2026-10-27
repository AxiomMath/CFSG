module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUElem

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U (barEq barEq_apply map_bar_fmap exists_fmap_of_bar
  fmap_injective conj_mem_commutator_isometryGroup_of_similitude)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL orthComponentData
  isSubnormal_subgroupOf_of_normalizes mul_conj_mul_inv)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {d : ℕ}

abbrev wK (wF : Fin d → h.fixedField) : Fin d → K := fun i => (wF i : K)

theorem wK_ne_zero {wF : Fin d → h.fixedField} (hwF : ∀ i, wF i ≠ 0) :
    ∀ i, wK h wF i ≠ 0 := fun i e => hwF i (Subtype.ext e)

@[expose] def barPair (h2 : (2 : K) ≠ 0) {wF : Fin d → h.fixedField} (hwF : ∀ i, wF i ≠ 0) :
    similarityPairs (oQ (diagGL (wK_ne_zero h hwF))) :=
  ⟨SemidirectProduct.inr (barEq h), (mem_similarityPairs_oQ h2 _ (diagGL_transpose _) _).2
    ⟨1, by
      change ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ * _ * (1 : GL (Fin d) K) =
        _ • ((diagGL (wK_ne_zero h hwF) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map
          (barEq h)
      rw [Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one, coe_diagGL,
        Units.val_one, one_smul, diagonal_map (map_zero _)]
      congr 1
      funext i
      exact ((wF i).2).symm⟩⟩

theorem barPair_left (h2 : (2 : K) ≠ 0) {wF : Fin d → h.fixedField} (hwF : ∀ i, wF i ≠ 0) :
    (barPair h h2 hwF).val.left = 1 := rfl

theorem barPair_right (h2 : (2 : K) ≠ 0) {wF : Fin d → h.fixedField} (hwF : ∀ i, wF i ≠ 0) :
    (barPair h h2 hwF).val.right = barEq h := rfl

abbrev iotaF : GL (Fin d) h.fixedField →* GL (Fin d) K :=
  GeneralLinearGroup.map h.fixedField.subtype

theorem coe_iotaF (X : GL (Fin d) h.fixedField) :
    ((iotaF h X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (X : Matrix (Fin d) (Fin d) h.fixedField).map h.fixedField.subtype := rfl

theorem iotaF_injective : Function.Injective (iotaF h (d := d)) := by
  intro X Y hXY
  apply Units.ext
  exact fmap_injective h (congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hXY)

theorem iotaF_mem_iso {wF : Fin d → h.fixedField} (hwF : ∀ i, wF i ≠ 0)
    {X : GL (Fin d) h.fixedField}
    (hX : X ∈ CatalogueBGraphForm.isometryGroup d h.fixedField (diagGL hwF)) :
    iotaF h X ∈ CatalogueBGraphForm.isometryGroup d K (diagGL (wK_ne_zero h hwF)) := by
  rw [CatalogueBGraphForm.mem_isometryGroup] at hX ⊢
  rw [coe_iotaF, coe_diagGL]
  rw [coe_diagGL] at hX
  have e := congrArg (fun M : Matrix (Fin d) (Fin d) h.fixedField => M.map h.fixedField.subtype) hX
  simp only [Matrix.map_mul, transpose_map, diagonal_map (map_zero _)] at e
  exact e

abbrev omegaF {wF : Fin d → h.fixedField} (hwF : ∀ i, wF i ≠ 0) : Subgroup (GL (Fin d) K) :=
  (⁅CatalogueBGraphForm.isometryGroup d h.fixedField (diagGL hwF),
    CatalogueBGraphForm.isometryGroup d h.fixedField (diagGL hwF)⁆).map (iotaF h)

theorem omegaF_le (h2 : (2 : K) ≠ 0) {wF : Fin d → h.fixedField} (hwF : ∀ i, wF i ≠ 0) :
    omegaF h hwF ≤ matrixDerived (oQ (diagGL (wK_ne_zero h hwF))) := by
  rw [matrixDerived_oQ h2 _ (diagGL_transpose _), omegaF, Subgroup.map_commutator]
  apply commutator_mono <;> rintro _ ⟨X, hX, rfl⟩ <;> exact iotaF_mem_iso h hwF hX

theorem conj_mem_omegaF {wF : Fin d → h.fixedField} (hwF : ∀ i, wF i ≠ 0)
    {g : GL (Fin d) K}
    (hg : g ∈ CatalogueBGraphForm.isometryGroup d K (diagGL (wK_ne_zero h hwF)))
    {c : K} (hc : (g : Matrix (Fin d) (Fin d) K).map h.bar = c • (g : Matrix (Fin d) (Fin d) K))
    {X : GL (Fin d) K} (hX : X ∈ omegaF h hwF) : g * X * g⁻¹ ∈ omegaF h hwF := by
  have := h.finite
  have hg0 : (g : Matrix (Fin d) (Fin d) K) ≠ 0 ∨ IsEmpty (Fin d) := by
    rcases isEmpty_or_nonempty (Fin d) with hd | hd
    · exact Or.inr hd
    · left
      intro h0
      have := (Matrix.isUnits_det_units g).ne_zero
      rw [h0, det_zero] at this
      exact this rfl
  rcases hg0 with hg0 | hd
  swap
  · have : g = 1 := Subsingleton.elim _ _
    subst this
    simpa using hX
  have hcN : h.norm c = 1 := by
    have e1 : (g : Matrix (Fin d) (Fin d) K) = ((g : Matrix (Fin d) (Fin d) K).map h.bar).map
        h.bar := by
      ext i j
      simp [h.bar_bar]
    rw [hc, show (c • (g : Matrix (Fin d) (Fin d) K)).map h.bar = h.bar c •
      (g : Matrix (Fin d) (Fin d) K).map h.bar by ext i j; simp [map_mul], hc, smul_smul] at e1
    have e2 : (1 - h.bar c * c) • (g : Matrix (Fin d) (Fin d) K) = 0 := by
      rw [sub_smul, one_smul, ← e1, sub_self]
    rcases smul_eq_zero.1 e2 with e3 | e3
    · rw [UnitaryFieldData.norm, mul_comm]
      linear_combination -e3
    · exact absurd e3 hg0
  obtain ⟨r, hr0, hr⟩ := h.exists_div_bar_eq hcN
  have hbr0 : h.bar r ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hfix : (r • (g : Matrix (Fin d) (Fin d) K)).map h.bar =
      r • (g : Matrix (Fin d) (Fin d) K) := by
    rw [show (r • (g : Matrix (Fin d) (Fin d) K)).map h.bar = h.bar r •
      (g : Matrix (Fin d) (Fin d) K).map h.bar by ext i j; simp [map_mul], hc, smul_smul, ← hr]
    congr 1
    field_simp
  obtain ⟨Y, hY⟩ := exists_fmap_of_bar h hfix
  have hYi : ∃ Yi : Matrix (Fin d) (Fin d) h.fixedField,
      Yi.map h.fixedField.subtype = r⁻¹ • ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    refine exists_fmap_of_bar h ?_
    have hgi : ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar =
        c⁻¹ • ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      have hc0 : c ≠ 0 := fun h0 => by
        rw [h0, UnitaryFieldData.norm, zero_mul] at hcN
        exact zero_ne_one hcN
      have e1 : (g : Matrix (Fin d) (Fin d) K).map h.bar *
          ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar = 1 := by
        rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [hc, Matrix.smul_mul] at e1
      calc ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar =
          (((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * g) *
            ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        _ = c⁻¹ • ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.mul_assoc]
            have : (g : Matrix (Fin d) (Fin d) K) *
                ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar = c⁻¹ • 1 := by
              rw [← one_smul K ((g : Matrix (Fin d) (Fin d) K) *
                ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar),
                ← inv_mul_cancel₀ hc0, mul_smul, e1]
            rw [this, Matrix.mul_smul, Matrix.mul_one]
    rw [show (r⁻¹ • ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).map h.bar =
      h.bar r⁻¹ • ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar by
        ext i j; simp [map_mul], hgi, smul_smul, map_inv₀, ← hr]
    congr 1
    field_simp
  obtain ⟨Yi, hYi⟩ := hYi
  have hYYi : Y * Yi = 1 := by
    apply fmap_injective h
    simp only [Matrix.map_mul, hY, hYi, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Matrix.smul_mul, Matrix.mul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      smul_smul, mul_inv_cancel₀ hr0, one_smul]
  have hYiY : Yi * Y = 1 := mul_eq_one_comm.1 hYYi
  set YG : GL (Fin d) h.fixedField := ⟨Y, Yi, hYYi, hYiY⟩ with hYG
  have hιY : iotaF h YG = GeneralLinearGroup.scalar (Fin d) (Units.mk0 r hr0) * g := by
    apply Units.ext
    rw [coe_iotaF, Units.val_mul, GeneralLinearGroup.coe_scalar]
    change Y.map h.fixedField.subtype = _
    rw [hY, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hrr : r * r ∈ h.fixedField := by
    have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 hg
    rw [coe_diagGL] at hiso
    obtain ⟨i⟩ : Nonempty (Fin d) := by
      by_contra hne
      exact hg0 (Subsingleton.elim (h := by
        have : IsEmpty (Fin d) := not_nonempty_iff.1 hne
        infer_instance) _ _)
    have e1 : (Y.map h.fixedField.subtype)ᵀ * diagonal (wK h wF) * Y.map h.fixedField.subtype =
        (r * r) • diagonal (wK h wF) := by
      rw [hY, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hiso, smul_smul]
    have e2 := congrFun (congrFun e1 i) i
    rw [Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul] at e2
    have hw0 : wK h wF i ≠ 0 := wK_ne_zero h hwF i
    have : r * r = ((Y.map h.fixedField.subtype)ᵀ * diagonal (wK h wF) *
        Y.map h.fixedField.subtype) i i / wK h wF i := by
      rw [e2]; field_simp
    rw [this]
    refine div_mem ?_ (wF i).2
    have hd : ((Y.map h.fixedField.subtype)ᵀ * diagonal (wK h wF) *
        Y.map h.fixedField.subtype) = (Yᵀ * diagonal wF * Y).map h.fixedField.subtype := by
      simp only [Matrix.map_mul, transpose_map, diagonal_map (map_zero _)]
      rfl
    rw [hd, map_apply]
    exact (_ : h.fixedField).2
  set μ : h.fixedField := ⟨r * r, hrr⟩ with hμ
  have hμ0 : μ ≠ 0 := fun e => mul_ne_zero hr0 hr0 (congrArg Subtype.val e)
  have hsim : (YG : Matrix (Fin d) (Fin d) h.fixedField)ᵀ * (diagGL hwF : GL (Fin d) h.fixedField) *
      (YG : Matrix (Fin d) (Fin d) h.fixedField) =
        μ • ((diagGL hwF : GL (Fin d) h.fixedField) : Matrix (Fin d) (Fin d) h.fixedField) := by
    apply fmap_injective h
    have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 hg
    rw [coe_diagGL] at hiso
    simp only [coe_diagGL, Matrix.map_mul, transpose_map, diagonal_map (map_zero _)]
    change (Y.map h.fixedField.subtype)ᵀ * diagonal (wK h wF) * Y.map h.fixedField.subtype =
      (μ • diagonal wF).map h.fixedField.subtype
    rw [hY, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hiso, smul_smul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, diagonal_apply, smul_eq_mul, hμ]
    split_ifs <;> simp
  obtain ⟨X₀, hX₀, rfl⟩ := hX
  have e := conj_mem_commutator_isometryGroup_of_similitude hsim hμ0 hX₀
  refine ⟨YG * X₀ * YG⁻¹, e, ?_⟩
  rw [map_mul, map_mul, map_inv, hιY]
  set sc := GeneralLinearGroup.scalar (Fin d) (Units.mk0 r hr0)
  have hs : ∀ M : GL (Fin d) K, sc * M * sc⁻¹ = M := fun M => by
    rw [← (commute_scalar (Units.mk0 r hr0) M).eq, mul_inv_cancel_right]
  calc sc * g * iotaF h X₀ * (sc * g)⁻¹ = sc * (g * iotaF h X₀ * g⁻¹) * sc⁻¹ := by group
    _ = g * iotaF h X₀ * g⁻¹ := hs _

end CFSG.ComponentClassification.Burgoyne.O
