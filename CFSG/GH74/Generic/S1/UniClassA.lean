module

public import CFSG.GH74.Generic.S1.UniPaired
public import CFSG.GH74.Generic.S1.Defs

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

@[expose] noncomputable def barEquiv (h : UnitaryFieldData p f F) : F ≃+* F :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩

theorem barEquiv_apply (h : UnitaryFieldData p f F) (c : F) : barEquiv h c = h.bar c := rfl

theorem cT_eq_conjTr (h : UnitaryFieldData p f F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    cT h M = CFSG.LieType.Universal.Unitary.conjTr (barEquiv h) M := rfl

theorem cT_blk4 (h : UnitaryFieldData p f F) (X Y : Matrix (Fin 2) (Fin 2) F) :
    cT h (blk4 X Y) = blk4 (cT h X) (cT h Y) := by
  simp only [cT_eq_conjTr]
  exact conjTr_blk4 (barEquiv h) X Y

theorem cT_wMat (h : UnitaryFieldData p f F) : cT h (wMat : Matrix (Fin 4) (Fin 4) F) = wMat := by
  rw [cT_eq_conjTr]
  exact conjTr_wMat (barEquiv h)

@[expose] noncomputable def leviHom (h : UnitaryFieldData p f F) :
    SpecialLinearGroup (Fin 2) F →* GL (Fin 4) F :=
  (diagGLHom F).comp (MonoidHom.prod SpecialLinearGroup.toGL
    ((Matrix.GeneralLinearGroup.inverseTranspose (n := Fin 2) (A := F)).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.map (h.bar : F →+* F)).comp SpecialLinearGroup.toGL)))

theorem leviHom_apply (h : UnitaryFieldData p f F) (X : SpecialLinearGroup (Fin 2) F) :
    leviHom h X = diagGL (SpecialLinearGroup.toGL X)
      (Matrix.GeneralLinearGroup.inverseTranspose
        (Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (SpecialLinearGroup.toGL X))) := rfl

theorem levi_block (h : UnitaryFieldData p f F) (X : SpecialLinearGroup (Fin 2) F) :
    ((Matrix.GeneralLinearGroup.inverseTranspose
        (Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (SpecialLinearGroup.toGL X)) :
          GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      cT h (((SpecialLinearGroup.toGL X)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, ← map_inv]
  rfl

theorem levi_val (h : UnitaryFieldData p f F) (X : SpecialLinearGroup (Fin 2) F) :
    ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blk4 (X : Matrix (Fin 2) (Fin 2) F)
        (cT h (((SpecialLinearGroup.toGL X)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
  rw [leviHom_apply, coe_diagGL, levi_block]
  rfl

theorem levi_unitary (h : UnitaryFieldData p f F) (X : SpecialLinearGroup (Fin 2) F) :
    cT h ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * wMat *
      ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = wMat := by
  rw [levi_val, cT_blk4]
  set Xm : Matrix (Fin 2) (Fin 2) F := (X : Matrix (Fin 2) (Fin 2) F) with hXm
  set Xi : Matrix (Fin 2) (Fin 2) F :=
    (((SpecialLinearGroup.toGL X)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hXi
  have h1 : Xi * Xm = 1 := by
    simp [hXi, hXm]
  have hsw : ∀ A B : Matrix (Fin 2) (Fin 2) F, blk4 A B * wMat = wMat * blk4 B A := by
    intro A B
    calc blk4 A B * wMat = wMat * (wMat * blk4 A B * wMat) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, wMat_mul_self, Matrix.one_mul]
      _ = wMat * blk4 B A := by rw [wMat_mul_blk4_mul_wMat]
  rw [hsw, cT_cT, Matrix.mul_assoc, blk4_mul, ← cT_mul, h1, cT_one, blk4_one, Matrix.mul_one]

theorem conj_levi_mem (h : UnitaryFieldData p f F) {P : GL (Fin 4) F}
    (hP : cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = wMat)
    (X : SpecialLinearGroup (Fin 2) F) :
    P * leviHom h X * P⁻¹ ∈ StatedSU 4 (p ^ f) F := by
  have hPi : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      wMat * cT h (P : Matrix (Fin 4) (Fin 4) F) := by
    have h1 : (wMat * cT h (P : Matrix (Fin 4) (Fin 4) F)) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [Matrix.mul_assoc, hP, wMat_mul_self]
    exact Units.inv_eq_of_mul_eq_one_left h1
  have hPPi : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [show StatedSU 4 (p ^ f) F = unitarySU p f F 4 from rfl, mem_unitarySU_iff h]
  have hcw : cT h (wMat : Matrix (Fin 4) (Fin 4) F) = wMat := cT_wMat h
  have hdetcT : ∀ M : Matrix (Fin 2) (Fin 2) F, (cT h M).det = h.bar M.det := fun M => by
    rw [cT, Matrix.det_transpose]
    exact (RingHom.map_det (h.bar : F →+* F) M).symm
  have hPPi' : (P : Matrix (Fin 4) (Fin 4) F) * (wMat * cT h (P : Matrix (Fin 4) (Fin 4) F)) = 1 := by
    rw [← hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj, levi_val, det_blk4]
    have h1 : (((SpecialLinearGroup.toGL X)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (X : Matrix (Fin 2) (Fin 2) F) = 1 := by simp
    have hX1 : (X : Matrix (Fin 2) (Fin 2) F).det = 1 := X.det_coe
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, hX1, mul_one, Matrix.det_one] at h2
    rw [hdetcT, h2, hX1, map_one, one_mul]
  · rw [Units.val_mul, Units.val_mul, hPi]
    have hL := levi_unitary h X
    have e1 : cT h ((P : Matrix (Fin 4) (Fin 4) F) *
        ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (wMat * cT h (P : Matrix (Fin 4) (Fin 4) F))) =
        (P : Matrix (Fin 4) (Fin 4) F) * wMat *
          cT h ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            cT h (P : Matrix (Fin 4) (Fin 4) F) := by
      rw [cT_mul, cT_mul, cT_mul, cT_cT, hcw]
      simp only [Matrix.mul_assoc]
    rw [← cT_def h, e1]
    calc (P : Matrix (Fin 4) (Fin 4) F) * wMat *
          cT h ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            cT h (P : Matrix (Fin 4) (Fin 4) F) *
        ((P : Matrix (Fin 4) (Fin 4) F) *
          ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            (wMat * cT h (P : Matrix (Fin 4) (Fin 4) F)))
        = (P : Matrix (Fin 4) (Fin 4) F) * wMat *
          (cT h ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            (cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F)) *
              ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) *
            (wMat * cT h (P : Matrix (Fin 4) (Fin 4) F)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hP, hL]
        simp only [Matrix.mul_assoc, wMat_mul_self, Matrix.mul_one]
        exact hPPi'

@[expose] noncomputable def iotaHom (h : UnitaryFieldData p f F) {P : GL (Fin 4) F}
    (hP : cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = wMat) :
    SpecialLinearGroup (Fin 2) F →* ↥(StatedSU 4 (p ^ f) F) :=
  ((MulAut.conj P).toMonoidHom.comp (leviHom h)).codRestrict _ (fun X => conj_levi_mem h hP X)

theorem iotaHom_val (h : UnitaryFieldData p f F) {P : GL (Fin 4) F}
    (hP : cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = wMat)
    (X : SpecialLinearGroup (Fin 2) F) :
    ((iotaHom h hP X : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = P * leviHom h X * P⁻¹ := rfl

theorem goodFixedCentral_of_paired (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (hq4 : p ^ f % 4 = 1)
    (α : MulAut ↥(StatedSU 4 (p ^ f) F)) {Bm : Matrix (Fin 4) (Fin 4) F} (hBB : Bm * Bm = 1)
    (hBu : cT h Bm * Bm = -1)
    (hα : ∀ k : ↥(StatedSU 4 (p ^ f) F),
      (((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        Bm * ((k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Bm) :
    GoodFixedCentral False α := by
  classical
  have hfin : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  obtain ⟨P, hP1, hP2⟩ := exists_paired_basis h hp2 hBB hBu
  let ι := iotaHom h hP1
  have hPi : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      wMat * cT h (P : Matrix (Fin 4) (Fin 4) F) := by
    have h1 : (wMat * cT h (P : Matrix (Fin 4) (Fin 4) F)) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [Matrix.mul_assoc, hP1, wMat_mul_self]
    exact Units.inv_eq_of_mul_eq_one_left h1
  have hPPi : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set D : Matrix (Fin 4) (Fin 4) F := blk4 (1 : Matrix (Fin 2) (Fin 2) F) (-1) with hD
  have hBPi : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Bm =
      D * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    calc ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Bm
        = ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (Bm * ((P : Matrix (Fin 4) (Fin 4) F) *
          ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))) := by rw [hPPi, Matrix.mul_one]
      _ = D * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        rw [← Matrix.mul_assoc Bm, hP2]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc _ (P : Matrix (Fin 4) (Fin 4) F), hPiP, Matrix.one_mul]
  refine ⟨ι.range, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨X, rfl⟩
    apply Subtype.ext
    apply Units.ext
    rw [hα, iotaHom_val, Units.val_mul, Units.val_mul]
    set Lm : Matrix (Fin 4) (Fin 4) F := ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
      with hLm
    have hDL : D * Lm = Lm * D := by
      rw [hD, hLm, levi_val, blk4_mul, blk4_mul]
      simp
    have hcomm : Bm * ((P : Matrix (Fin 4) (Fin 4) F) * Lm *
        ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) =
        ((P : Matrix (Fin 4) (Fin 4) F) * Lm * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * Bm := by
      calc Bm * ((P : Matrix (Fin 4) (Fin 4) F) * Lm * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
          = (Bm * (P : Matrix (Fin 4) (Fin 4) F)) * Lm * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
            simp only [Matrix.mul_assoc]
        _ = (P : Matrix (Fin 4) (Fin 4) F) * (D * Lm) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
            rw [hP2]; simp only [Matrix.mul_assoc]
        _ = (P : Matrix (Fin 4) (Fin 4) F) * Lm * (D * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
            rw [hDL]; simp only [Matrix.mul_assoc]
        _ = ((P : Matrix (Fin 4) (Fin 4) F) * Lm * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * Bm := by
            rw [← hBPi]; simp only [Matrix.mul_assoc]
    rw [hcomm, Matrix.mul_assoc _ Bm Bm, hBB, Matrix.mul_one]
  · intro z hz
    have hz' := (mem_center_statedSU_four_iff hF hq4 z).1 hz
    rcases hz' with h1 | h1
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      rw [iotaHom_val, map_one, mul_one, mul_inv_cancel, h1]
    · let negOne : SpecialLinearGroup (Fin 2) F := ⟨-1, by rw [Matrix.det_neg, Matrix.det_one]; norm_num⟩
      have hneg : ((SpecialLinearGroup.toGL negOne)⁻¹ : GL (Fin 2) F) =
          SpecialLinearGroup.toGL negOne := by
        apply inv_eq_of_mul_eq_one_right
        apply Units.ext
        show (-1 : Matrix (Fin 2) (Fin 2) F) * (-1) = 1
        rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.one_mul]
      have hlev : leviHom h negOne = xGL F := by
        apply Units.ext
        rw [levi_val, hneg, xGL_eq_neg_one]
        change blk4 (-1) (cT h (-1)) = -1
        rw [cT_neg, cT_one, blk4_neg, blk4_one]
      refine ⟨negOne, ?_⟩
      apply Subtype.ext
      rw [iotaHom_val, hlev, h1, ← xGL_comm P, mul_inv_cancel_right]
  · have h3 : 3 ≤ p := by
      have := h.prime.two_le
      omega
    have hq3 : 3 ≤ p ^ f := le_trans h3 (Nat.le_self_pow (by have := h.one_le; omega) p)
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      nlinarith
    have hSL : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
      CFSG.ClassicalInvolution.sl2_isPerfect h4
    exact Or.inl (Subgroup.isPerfect_iff.1 (Group.IsPerfect.range ι))

end CFSG.GH74.Generic.S1.Uni
