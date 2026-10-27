module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Pair
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4Nc
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4T2

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks UnitaryOut UnitaryConj Subgroup

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {P : GL (Fin 4) K}
  (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)

theorem ker_pairHom :
    ((QuotientGroup.mk' (scal p f K)).comp (pairHom h hP)).ker =
      center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro ha
    obtain ⟨c, hc⟩ := val_of_mem_scal ha
    have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e : bd (a : Matrix (Fin 2) (Fin 2) K) (dualU h a) = (c : K) • 1 := by
      rw [← cP_pairHom h hP a, cP, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
    have ea : (a : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
      have e1 := congrArg ul e
      rw [ul_bd] at e1
      rw [e1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ul]
    refine Subgroup.mem_center_iff.mpr fun b => Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ea, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  · intro ha
    obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp ha
    rw [Fintype.card_fin] at hr2
    have hra : (a : Matrix (Fin 2) (Fin 2) K) = r • 1 := by
      rw [← hr, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hbr : h.bar r = r := by
      have h1 : (r - 1) * (r + 1) = 0 := by linear_combination hr2
      rcases mul_eq_zero.1 h1 with h0 | h0
      · rw [sub_eq_zero.1 h0, map_one]
      · rw [eq_neg_of_add_eq_zero_left h0, map_neg, map_one]
    have hr0 : r ≠ 0 := by
      rintro rfl
      norm_num at hr2
    have hd : dualU h a = r • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [dualU, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, hra, hbr]
    have hbd : bd (r • (1 : Matrix (Fin 2) (Fin 2) K)) (r • 1) = r • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [bd]
    show ((pairHom h hP a : unitarySU p f K 4) : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, val_pairHom, hra, hd, hbd, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem isSimpleGroup_range_pairHom :
    IsSimpleGroup ((QuotientGroup.mk' (scal p f K)).comp (pairHom h hP)).range := by
  have : Finite K := h.finite
  exact L4U4.isSimpleGroup_range_of_ker_eq_center (four_le_card h) _ (ker_pairHom h hP)

theorem isPerfect_range_pairHom :
    Group.IsPerfect ((QuotientGroup.mk' (scal p f K)).comp (pairHom h hP)).range := by
  have : Finite K := h.finite
  exact L4U4.isPerfect_range_of_ker_eq_center (four_le_card h) _ (ker_pairHom h hP)

theorem noOddNormal_range_pairHom :
    NoOddNormal ((QuotientGroup.mk' (scal p f K)).comp (pairHom h hP)).range := by
  have : Finite K := h.finite
  have := isSimpleGroup_range_pairHom h hP
  have := isPerfect_range_pairHom h hP
  exact noOddNormal_of_isSimpleGroup Q5L4.exists_ne_comm_of_perfect

include h in
theorem isBD_cP_of_comm_pair (hp2 : p ≠ 2) {X : unitarySU p f K 4} {l : K} (hl0 : l ≠ 0)
    (hX : cP P X = X1 l) {c : unitarySU p f K 4} (hc : c * X = X * c) : IsBD (cP P c) := by
  have hm := congrArg (cP P) hc
  rw [cP_mul, cP_mul, hX] at hm
  exact isBD_of_comm_X1 (two_ne_zero_of_odd h hp2) hl0 hm

include h in
@[expose] noncomputable def ulHomPair (hp2 : p ≠ 2) {X : unitarySU p f K 4} {l : K}
    (hl0 : l ≠ 0) (hX : cP P X = X1 l) :
    centralizer ({X} : Set (unitarySU p f K 4)) →* Matrix (Fin 2) (Fin 2) K where
  toFun c := ul (cP P c.1)
  map_one' := by
    change ul (cP P 1) = 1
    rw [cP_one, ul_one]
  map_mul' := fun c d => by
    have hc := isBD_cP_of_comm_pair h hp2 hl0 hX (mem_centralizer_singleton_iff.mp c.2)
    have hd := isBD_cP_of_comm_pair h hp2 hl0 hX (mem_centralizer_singleton_iff.mp d.2)
    change ul (cP P (c.1 * d.1)) = ul (cP P c.1) * ul (cP P d.1)
    rw [cP_mul, ul_mul hc hd]

theorem exists_blockDet_pair (hp2 : p ≠ 2) {X : unitarySU p f K 4} {l : K} (hl0 : l ≠ 0)
    (hX : cP P X = X1 l) :
    ∃ δ : centralizer ({X} : Set (unitarySU p f K 4)) →* Kˣ,
      ∀ c : centralizer ({X} : Set (unitarySU p f K 4)), δ c = 1 →
        (c : unitarySU p f K 4) ∈ (pairHom h hP).range := by
  refine ⟨(Matrix.detMonoidHom.comp (ulHomPair h hp2 hl0 hX)).toHomUnits, fun c hc => ?_⟩
  have h1 := congrArg Units.val hc
  rw [MonoidHom.coe_toHomUnits, Units.val_one, MonoidHom.comp_apply] at h1
  have hdu : (ul (cP P c.1)).det = 1 := h1
  have hBD := isBD_cP_of_comm_pair h hp2 hl0 hX (mem_centralizer_singleton_iff.mp c.2)
  have e1 := ulStar_mul_lr h hBD (unitary_cP h P hP c.1)
  obtain ⟨a, ha⟩ : ∃ a : Matrix.SpecialLinearGroup (Fin 2) K,
      (a : Matrix (Fin 2) (Fin 2) K) = ul (cP P c.1) := ⟨⟨ul (cP P c.1), hdu⟩, rfl⟩
  have e2 := star_mul_dualU h a
  rw [ha] at e2
  have e3 : lr (cP P c.1) * ((ul (cP P c.1)).map h.bar)ᵀ = 1 := mul_eq_one_comm.mp e1
  have hlr : dualU h a = lr (cP P c.1) := by
    calc dualU h a = (lr (cP P c.1) * ((ul (cP P c.1)).map h.bar)ᵀ) * dualU h a := by
          rw [e3, Matrix.one_mul]
      _ = lr (cP P c.1) := by rw [Matrix.mul_assoc, e2, Matrix.mul_one]
  refine ⟨a, ?_⟩
  apply eq_of_cP_eq P
  rw [cP_pairHom, hlr, ha]
  exact (eq_bd hBD).symm

theorem le_range_pairHom_of_perfect (hp2 : p ≠ 2) {X : unitarySU p f K 4} {l : K} (hl0 : l ≠ 0)
    (hX : cP P X = X1 l) {M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hM : M ≤ centralizer {QuotientGroup.mk' (scal p f K) X}) (hMp : ⁅M, M⁆ = M) :
    M ≤ ((QuotientGroup.mk' (scal p f K)).comp (pairHom h hP)).range := by
  obtain ⟨δ, hδ⟩ := exists_blockDet_pair h hP hp2 hl0 hX
  exact le_map_range_of_blockDet (pairHom h hP) δ hδ hM hMp

theorem blk_zero_eq_bd (x y : K) : blk x 0 0 y = bd (x • 1) (y • 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, bd]

theorem blk_mul_map_bar {b f : K} (hbf : b * h.bar f = 1) :
    blk 0 b f 0 * (blk 0 b f 0).map h.bar = -1 := by
  have hfb : f * h.bar b = 1 := by
    have e := congrArg h.bar hbf
    rw [map_mul, h.bar_bar, map_one] at e
    linear_combination e
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | linear_combination -hbf | linear_combination -hfb
    | linear_combination hbf | linear_combination hfb

theorem trace_uU (c : K) :
    (((uU h P hP c : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4 := by
  rw [uU, val_hypSU, StabU.trace_conj, trace_U12]

theorem trace_uL (c : K) :
    (((uL h P hP c : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4 := by
  rw [uL, val_hypSU, StabU.trace_conj, trace_U21]

end CFSG.ClassicalInvolution.Q3.TA3.Q5U4
