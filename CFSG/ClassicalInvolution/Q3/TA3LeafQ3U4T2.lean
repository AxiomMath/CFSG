module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4T2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTU4

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

namespace Q3U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks UnitaryOut
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

omit [Field K] in
theorem transpose_swapM_bJ {L : Type} [Field L] :
    (Q3L4.swapM : Matrix (Fin 4) (Fin 4) L)ᵀ * bJ 1 1 * Q3L4.swapM = bJ 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q3L4.swapM, bJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem map_bar_swapM : (Q3L4.swapM : Matrix (Fin 4) (Fin 4) K).map h.bar = Q3L4.swapM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q3L4.swapM]

variable {R : GL (Fin 4) K} {t : K}
  (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)

include hR in
theorem conj_swapM_mem :
    R * toGL Q3L4.swapM Q3L4.det_swapM * R⁻¹ ∈ unitarySU p f K 4 := by
  have hRR : (R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [mem_unitarySU_iff h, Units.val_mul, Units.val_mul, coe_toGL]
  refine ⟨?_, ?_⟩
  · rw [det_mul, det_mul, Q3L4.det_swapM, mul_one, ← det_mul, hRR, det_one]
  · change uStar h _ * _ = 1
    have hX : uStar h (Q3L4.swapM : Matrix (Fin 4) (Fin 4) K) = Q3L4.swapMᵀ := by
      rw [uStar, map_bar_swapM]
    have hRi : uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * uStar h (R : Matrix (Fin 4) (Fin 4) K)
        = 1 := by rw [← uStar_mul, hRR, uStar_one]
    rw [uStar_mul, uStar_mul, hX]
    calc uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((Q3L4.swapM : Matrix (Fin 4) (Fin 4) K)ᵀ *
          uStar h (R : Matrix (Fin 4) (Fin 4) K)) *
          ((R : Matrix (Fin 4) (Fin 4) K) * Q3L4.swapM * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((Q3L4.swapM : Matrix (Fin 4) (Fin 4) K)ᵀ *
          (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
          Q3L4.swapM) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
      _ = uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
          rw [hR, Matrix.mul_smul, Matrix.smul_mul, transpose_swapM_bJ]
      _ = 1 := by rw [← Matrix.mul_assoc, hRi, Matrix.one_mul, hRR]

@[expose] noncomputable def swU : unitarySU p f K 4 :=
  ⟨R * toGL Q3L4.swapM Q3L4.det_swapM * R⁻¹, conj_swapM_mem h hR⟩

theorem cP_swU : cP R (swU h hR) = Q3L4.swapM := by
  change (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
    ((R * toGL Q3L4.swapM Q3L4.det_swapM * R⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (R : Matrix (Fin 4) (Fin 4) K) = Q3L4.swapM
  rw [Units.val_mul, Units.val_mul, coe_toGL, inv_mul_val_mul]

theorem swU_mul_swU : swU h hR * swU h hR = 1 :=
  eq_of_cP_eq R (by rw [cP_mul, cP_swU, Q3L4.swapM_mul_swapM, cP_one])

theorem swU_conj (a b : SL(2, h.fixedField)) :
    swU h hR * bdHomU h hR (a, b) * swU h hR = bdHomU h hR (b, a) :=
  eq_of_cP_eq R (by
    rw [cP_mul, cP_mul, cP_swU, cP_bdHomU, cP_bdHomU, bdK, bdK, Q3L4.swapM_mul_bd,
      Matrix.mul_assoc, Q3L4.swapM_mul_swapM, Matrix.mul_one])

variable {X : unitarySU p f K 4}
  (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
    (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))

include hXR in
theorem val_swU_mul_X :
    (((swU h hR * X : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (-1 : K) • (((X * swU h hR : unitarySU p f K 4) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) := by
  rw [val_eq_cP R (swU h hR * X), val_eq_cP R (X * swU h hR), cP_mul, cP_mul, cP_swU, cP_X hXR,
    Q3L4.swapM_mul_X1, Matrix.mul_smul, Matrix.smul_mul]

omit h in
theorem mk_eq_of_smul {A B : unitarySU p f K 4} {c : K}
    (hB : ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      c • ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    (QuotientGroup.mk A : StatedProj (StatedSU 4 (p ^ f) K)) = QuotientGroup.mk B := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := (Matrix.isUnits_det_units (B : GL (Fin 4) K)).ne_zero
    rw [hB, zero_smul, det_zero] at this
    exact this rfl
  rw [QuotientGroup.eq]
  show ((A⁻¹ * B : unitarySU p f K 4) : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hB,
    Matrix.mul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one]

include hR in
theorem ker_bdHomU_iff (a b : SL(2, h.fixedField)) :
    (QuotientGroup.mk (bdHomU h hR (a, b)) : StatedProj (StatedSU 4 (p ^ f) K)) = 1 ↔
      (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
  constructor
  · intro hx
    rw [QuotientGroup.eq_one_iff] at hx
    obtain ⟨c, hc⟩ := val_of_mem_scal hx
    have e : bdK h (a, b) = (c : K) • 1 := by
      rw [← cP_bdHomU h hR (a, b), cP, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have ea : (a : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype =
        (c : K) • 1 := by
      have e1 := congrArg ul e
      rw [bdK, ul_bd] at e1
      rw [e1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ul]
    have eb : (b : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype =
        (c : K) • 1 := by
      have e1 := congrArg lr e
      rw [bdK, lr_bd] at e1
      rw [e1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lr]
    have hab : a = b :=
      Subtype.ext (Matrix.map_injective (h.fixedField.subtype).injective (ea.trans eb.symm))
    subst hab
    obtain ⟨r, hr2, hr⟩ :=
      Matrix.SpecialLinearGroup.mem_center_iff.mp (mem_center_of_map_eq_smul h ea)
    rw [Fintype.card_fin] at hr2
    have h1 : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 h1 with h0 | h0
    · have ha : a = 1 := Subtype.ext (by
        rw [← hr, sub_eq_zero.1 h0, map_one, Matrix.SpecialLinearGroup.coe_one])
      exact Or.inl ⟨ha, ha⟩
    · have ha : a = -1 := Subtype.ext (by
        rw [← hr, eq_neg_of_add_eq_zero_left h0, map_neg, map_one,
          Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one])
      exact Or.inr ⟨ha, ha⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [show ((1 : SL(2, h.fixedField)), (1 : SL(2, h.fixedField))) = 1 from rfl, map_one,
        QuotientGroup.mk_one]
    · rw [QuotientGroup.eq_one_iff]
      have hb : bdK h (-1, -1) = -1 := by
        rw [bdK]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [bd]
      have e : bdHomU h hR (-1, -1) = negOne h := ext_val (by
        rw [val_bdHomU, hb, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul,
          mul_inv_cancel, Units.val_one]
        show _ = ((-1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        rw [Units.val_neg, Units.val_one])
      rw [e]
      exact negOne_mem_scal h

include hXR in
theorem mk_bdHomU_neg_one :
    (QuotientGroup.mk (bdHomU h hR (-1, 1)) : StatedProj (StatedSU 4 (p ^ f) K)) =
      QuotientGroup.mk X := by
  refine (mk_eq_of_smul (c := -1) ?_).symm
  have hb : bdK h (-1, 1) = (-1 : K) • X1 1 := by
    rw [bdK]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bd, X1]
  rw [val_eq_cP R (bdHomU h hR (-1, 1)), val_eq_cP R X, cP_bdHomU, cP_X hXR, hb,
    Matrix.mul_smul, Matrix.smul_mul]

end Q3U4

end CFSG.ClassicalInvolution.Q3.TA3
