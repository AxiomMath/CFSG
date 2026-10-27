module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3L
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3D
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TU4Bound
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TFrameU

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut StabU DiagU HBlocks TBlocks
open CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def dOne (s c : K) : Matrix (Fin 2) (Fin 2) K := !![1, s; c, -(c * s)]

theorem uStar_bd_dOne {s c : K} (hc : h.norm c = -1) (hs : h.bar s = -s) :
    uStar h (bd (dOne s c) (dOne s c)) * bd (dOne s c) (dOne s c) = (2 * s) • bJ 1 1 := by
  have hc' : c * h.bar c = -1 := hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uStar, bd, dOne, bJ, Matrix.mul_apply, Fin.sum_univ_four, hs] <;>
    first
    | ring1
    | linear_combination hc'
    | linear_combination s * hc'
    | linear_combination (-s) * hc'
    | linear_combination s ^ 2 * hc'
    | linear_combination (-s ^ 2) * hc'

include h in
theorem exists_frame_t2 (hp2 : p ≠ 2) (X : unitarySU p f K 4)
    (hXX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = 1)
    (h1 : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ 1)
    (hm1 : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ -1) :
    ∃ (R : GL (Fin 4) K) (t : K), t ≠ 0 ∧ h.bar t = -t ∧
      uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1 ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
        (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K) := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨Q, hQu, hXQ⟩ := exists_orthonormal_eigenframe h hp2 X hXX h1 hm1
  obtain ⟨c, hc⟩ := OddUnitaryInvolutionSylow.exists_norm_eq_neg_one h
  obtain ⟨s, hs0, hsb⟩ := OIU.exists_bar_neg h
  set D := bd (dOne s c) (dOne s c) with hD
  have hDD := uStar_bd_dOne h hc hsb
  have ht0 : 2 * s ≠ 0 := mul_ne_zero h2K hs0
  have ht : h.bar (2 * s) = -(2 * s) := by rw [map_mul, map_ofNat, hsb]; ring
  have hR1 : uStar h (Q * D) * (Q * D) = (2 * s) • bJ 1 1 := by
    rw [uStar_mul]
    calc uStar h D * uStar h Q * (Q * D) = uStar h D * (uStar h Q * Q) * D := by
          simp only [Matrix.mul_assoc]
      _ = (2 * s) • bJ 1 1 := by rw [hQu, Matrix.mul_one, hDD]
  have hdet : (Q * D).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hR1
    rw [det_mul, h0, mul_zero, det_smul, det_bJ, Fintype.card_fin] at this
    simp at this
    exact ht0 (pow_eq_zero_iff (by norm_num) |>.1 this.symm)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (Q * D) hdet, 2 * s, ht0, ht, ?_, ?_⟩
  · rw [GeneralLinearGroup.val_mkOfDetNeZero]
    exact hR1
  · rw [GeneralLinearGroup.val_mkOfDetNeZero, ← Matrix.mul_assoc, hXQ, Matrix.mul_assoc,
      Matrix.mul_assoc, ← bd_comm_X1]

theorem eq_of_map_eq {y z : SpecialLinearGroup (Fin 2) h.fixedField}
    (hyz : (y : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype =
      (z : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype) : y = z :=
  Subtype.ext (Matrix.map_injective (RingHom.injective _) hyz)

theorem map_one_fixed :
    ((1 : SpecialLinearGroup (Fin 2) h.fixedField) : Matrix (Fin 2) (Fin 2) h.fixedField).map
      h.fixedField.subtype = 1 := by
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_neg_one_fixed :
    ((-1 : SpecialLinearGroup (Fin 2) h.fixedField) : Matrix (Fin 2) (Fin 2) h.fixedField).map
      h.fixedField.subtype = -1 := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.map_neg _ (fun a => map_neg _ a), Matrix.map_one _ (map_zero _) (map_one _)]

variable {R : GL (Fin 4) K} {t : K}
  (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)

abbrev blU : SpecialLinearGroup (Fin 2) h.fixedField →* unitarySU p f K 4 :=
  (bdHomU h hR).comp (MonoidHom.inl _ _)

abbrev brU : SpecialLinearGroup (Fin 2) h.fixedField →* unitarySU p f K 4 :=
  (bdHomU h hR).comp (MonoidHom.inr _ _)

theorem cP_bdHomU (x : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) : cP R (bdHomU h hR x) = bdK h x := by
  have h1 : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [cP, val_bdHomU]
  simp only [← Matrix.mul_assoc]
  rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem cP_blU (a : SpecialLinearGroup (Fin 2) h.fixedField) :
    cP R (blU h hR a) =
      bd ((a : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype) 1 := by
  rw [MonoidHom.comp_apply, cP_bdHomU, bdK, MonoidHom.inl_apply, map_one_fixed]

theorem cP_brU (b : SpecialLinearGroup (Fin 2) h.fixedField) :
    cP R (brU h hR b) =
      bd 1 ((b : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype) := by
  rw [MonoidHom.comp_apply, cP_bdHomU, bdK, MonoidHom.inr_apply, map_one_fixed]

theorem blU_mul_brU (a b : SpecialLinearGroup (Fin 2) h.fixedField) :
    blU h hR a * brU h hR b = brU h hR b * blU h hR a := by
  simp only [MonoidHom.comp_apply, ← map_mul]
  congr 1
  ext <;> simp

variable {X : unitarySU p f K 4}
  (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
    (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))

include hXR in
theorem blU_comm (a : SpecialLinearGroup (Fin 2) h.fixedField) :
    blU h hR a * X = X * blU h hR a := by
  apply eq_of_cP_eq R
  rw [cP_mul, cP_mul, cP_blU, cP_X hXR, bd_comm_X1]

include hXR in
theorem brU_comm (b : SpecialLinearGroup (Fin 2) h.fixedField) :
    brU h hR b * X = X * brU h hR b := by
  apply eq_of_cP_eq R
  rw [cP_mul, cP_mul, cP_brU, cP_X hXR, bd_comm_X1]

include h hXR in
theorem exists_bd_of_commU (hp2 : p ≠ 2) {n : unitarySU p f K 4} (hn : n * X = X * n) :
    ∃ c d c' d' : Matrix (Fin 2) (Fin 2) K, cP R n = bd c d ∧ cP R n⁻¹ = bd c' d' ∧
      c * c' = 1 ∧ d * d' = 1 := by
  have hn' : n⁻¹ * X = X * n⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hn, mul_assoc, mul_inv_cancel, mul_one]
  have e1 := eq_bd (isBD_cP_of_comm h hp2 hXR hn)
  have e2 := eq_bd (isBD_cP_of_comm h hp2 hXR hn')
  refine ⟨_, _, _, _, e1, e2, ?_⟩
  have e3 : bd (ul (cP R n) * ul (cP R n⁻¹)) (lr (cP R n) * lr (cP R n⁻¹)) = bd 1 1 := by
    rw [← bd_mul, ← e1, ← e2, ← cP_mul, mul_inv_cancel, cP_one, bd_one]
  exact bd_inj e3

include hXR in
theorem conj_mem_range_bl (hp2 : p ≠ 2) (ht0 : t ≠ 0) {n : unitarySU p f K 4}
    (hn : n * X = X * n) (a : SpecialLinearGroup (Fin 2) h.fixedField) :
    ∃ a', n * blU h hR a * n⁻¹ = blU h hR a' := by
  obtain ⟨c, d, c', d', e1, e2, hcc, hdd⟩ := exists_bd_of_commU h hXR hp2 hn
  set am := (a : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype with ham
  have e4 : cP R (n * blU h hR a * n⁻¹) = bd (c * am * c') 1 := by
    rw [cP_mul, cP_mul, cP_blU, e1, e2, bd_mul, bd_mul, Matrix.mul_one, hdd]
  have hdu : (ul (cP R (n * blU h hR a * n⁻¹))).det = 1 := by
    have hda : am.det = 1 := det_map_fixed h a
    rw [e4, ul_bd, det_mul, det_mul, hda, mul_one, ← det_mul, hcc, det_one]
  obtain ⟨x, hx⟩ := mem_range_of_det_ul h ht0 hR (by rw [e4]; exact isBD_bd _ _) hdu
  refine ⟨x.1, ?_⟩
  have e5 := congrArg (cP R) hx
  rw [cP_bdHomU, e4, bdK] at e5
  obtain ⟨-, hx2⟩ := bd_inj e5
  have hx2' : x.2 = 1 := eq_of_map_eq h (by rw [hx2, map_one_fixed])
  rw [← hx, MonoidHom.comp_apply, MonoidHom.inl_apply]
  congr 1
  exact Prod.ext rfl hx2'

include hXR in
theorem conj_mem_range_br (hp2 : p ≠ 2) (ht0 : t ≠ 0) {n : unitarySU p f K 4}
    (hn : n * X = X * n) (b : SpecialLinearGroup (Fin 2) h.fixedField) :
    ∃ b', n * brU h hR b * n⁻¹ = brU h hR b' := by
  obtain ⟨c, d, c', d', e1, e2, hcc, hdd⟩ := exists_bd_of_commU h hXR hp2 hn
  set bm := (b : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype with hbm
  have e4 : cP R (n * brU h hR b * n⁻¹) = bd 1 (d * bm * d') := by
    rw [cP_mul, cP_mul, cP_brU, e1, e2, bd_mul, bd_mul, Matrix.mul_one, hcc]
  have hBD : IsBD (cP R (n * brU h hR b * n⁻¹)) := by rw [e4]; exact isBD_bd _ _
  have hdu : (ul (cP R (n * brU h hR b * n⁻¹))).det = 1 := by rw [e4, ul_bd, det_one]
  obtain ⟨x, hx⟩ := mem_range_of_det_ul h ht0 hR hBD hdu
  refine ⟨x.2, ?_⟩
  have e5 := congrArg (cP R) hx
  rw [cP_bdHomU, e4, bdK] at e5
  obtain ⟨hx1, -⟩ := bd_inj e5
  have hx1' : x.1 = 1 := eq_of_map_eq h (by rw [hx1, map_one_fixed])
  rw [← hx, MonoidHom.comp_apply, MonoidHom.inr_apply]
  congr 1
  exact Prod.ext hx1' rfl

theorem neg_one_inv_sl : (-1 : SpecialLinearGroup (Fin 2) h.fixedField)⁻¹ = -1 :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (by simp))

theorem eq_of_bl_br_scalar {a b : SpecialLinearGroup (Fin 2) h.fixedField}
    (hab : thU p f K (blU h hR a) = thU p f K (brU h hR b)) :
    (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
  obtain ⟨c, hc⟩ := val_of_mem_scal hab
  have h1 : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e1 : cP R ((blU h hR a)⁻¹ * brU h hR b) = (c : K) • 1 := by
    rw [cP, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]
  have e2 : (blU h hR a)⁻¹ * brU h hR b = bdHomU h hR (a⁻¹, b) := by
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, ← map_inv,
      ← map_mul]
    congr 1
    ext <;> simp
  have hsc : (c : K) • (1 : Matrix (Fin 4) (Fin 4) K) = bd ((c : K) • 1) ((c : K) • 1) := by
    rw [← scalar_eq_bd, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [e2, cP_bdHomU, bdK, hsc] at e1
  obtain ⟨ha, hb⟩ := bd_inj e1
  have hdet := det_map_fixed h a⁻¹
  rw [ha, det_smul, det_one, mul_one, Fintype.card_fin, pow_two] at hdet
  rcases mul_self_eq_one_iff.mp hdet with hc1 | hc1
  · rw [hc1, one_smul] at ha hb
    left
    refine ⟨?_, eq_of_map_eq h (by rw [hb, map_one_fixed])⟩
    exact inv_eq_one.mp (eq_of_map_eq h (by rw [ha, map_one_fixed]))
  · rw [hc1, neg_one_smul] at ha hb
    right
    refine ⟨?_, eq_of_map_eq h (by rw [hb, map_neg_one_fixed])⟩
    have ha' : a⁻¹ = -1 := eq_of_map_eq h (by rw [ha, map_neg_one_fixed])
    rw [← inv_inv a, ha', neg_one_inv_sl]

include hXR in
theorem blU_neg_one : blU h hR (-1) = negOneU h * X := by
  apply eq_of_cP_eq R
  rw [cP_blU, cP_mul, cP_X hXR, map_neg_one_fixed, X1_eq_bd]
  have e : cP R (negOneU h) = -1 := by
    rw [cP, coe_negOneU, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

include hXR in
theorem brU_neg_one : brU h hR (-1) = X := by
  apply eq_of_cP_eq R
  rw [cP_brU, cP_X hXR, map_neg_one_fixed, X1_eq_bd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

end CFSG.ComponentClassification.HarrisLit.C3
