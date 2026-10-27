module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6PA
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6PB
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow

open Matrix Subgroup CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem F4_mul_self_eq_one_imp : ∀ x : F4, x * x = 1 → x = 1 := by decide

theorem YK_normalizer_zero {m : SL(4, F4)} (hN : ∀ y ∈ YK, m * y * m⁻¹ ∈ YK) :
    m 0 2 = 0 ∧ m 0 3 = 0 ∧ m 1 2 = 0 ∧ m 1 3 = 0 := by
  obtain ⟨a₂, a₄, a₅, a₈, hc⟩ := hN (pSL 0 0 0 1 1 0) ⟨0, 1, 1, 0, rfl⟩
  have hmy : m * pSL 0 0 0 1 1 0 = pSL 0 a₂ 0 a₄ a₅ a₈ * m := by
    rw [← hc, inv_mul_cancel_right]
  have e00 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 0 0) hmy
  have e01 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 0 1) hmy
  have e10 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 1 0) hmy
  have e11 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 1 1) hmy
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_pSL, pMat, Matrix.mul_apply, Fin.sum_univ_four]
    at e00 e01 e10 e11
  exact ⟨by linear_combination e00, by linear_combination e01,
    by linear_combination e10, by linear_combination e11⟩

theorem exists_decomp_blocks {m : SL(4, F4)} (h02 : m 0 2 = 0) (h03 : m 0 3 = 0)
    (h12 : m 1 2 = 0) (h13 : m 1 3 = 0) (hA : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1) :
    ∃ (A B : SL(2, F4)) (y : SL(4, F4)), y ∈ YK ∧
      A 0 0 = m 0 0 ∧ A 0 1 = m 0 1 ∧ A 1 0 = m 1 0 ∧ A 1 1 = m 1 1 ∧
      m = y * (blockSL2 F4 3 0 A * blockSL2 F4 3 2 B) := by
  have hdetm : (m : Matrix (Fin 4) (Fin 4) F4).det = 1 := m.2
  have hB : m 2 2 * m 3 3 - m 2 3 * m 3 2 = 1 := by
    have h := hdetm
    have s10 : Fin.succAbove (1 : Fin 4) (0 : Fin 3) = 0 := by decide
    have s11 : Fin.succAbove (1 : Fin 4) (1 : Fin 3) = 2 := by decide
    have s12 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := by decide
    rw [Matrix.det_succ_row_zero] at h
    simp [Fin.sum_univ_succ, Matrix.det_fin_three, h02, h03, h12, h13, s10, s11, s12] at h
    linear_combination h - (m 2 2 * m 3 3 - m 2 3 * m 3 2) * hA
  obtain ⟨A, hA00, hA01, hA10, hA11⟩ : ∃ A : SL(2, F4), A 0 0 = m 0 0 ∧ A 0 1 = m 0 1 ∧
      A 1 0 = m 1 0 ∧ A 1 1 = m 1 1 :=
    ⟨⟨!![m 0 0, m 0 1; m 1 0, m 1 1], by rw [Matrix.det_fin_two_of]; exact hA⟩, rfl, rfl, rfl, rfl⟩
  obtain ⟨B, hB00, hB01, hB10, hB11⟩ : ∃ B : SL(2, F4), B 0 0 = m 2 2 ∧ B 0 1 = m 2 3 ∧
      B 1 0 = m 3 2 ∧ B 1 1 = m 3 3 :=
    ⟨⟨!![m 2 2, m 2 3; m 3 2, m 3 3], by rw [Matrix.det_fin_two_of]; exact hB⟩, rfl, rfl, rfl, rfl⟩
  refine ⟨A, B, pSL 0 (m 2 0 * m 0 1 + m 2 1 * m 0 0) 0 (m 2 0 * m 1 1 + m 2 1 * m 1 0)
    (m 3 1 * m 0 0 + m 3 0 * m 0 1) (m 3 0 * m 1 1 + m 3 1 * m 1 0),
    ⟨_, _, _, _, rfl⟩, hA00, hA01, hA10, hA11, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_pSL,
    pb_blockSL2_zero, pb_blockSL2_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pMat, Matrix.mul_apply, Fin.sum_univ_four, hA00, hA01, hA10, hA11, hB00, hB01, hB10,
      hB11]
  all_goals first
    | linear_combination h02
    | linear_combination h03
    | linear_combination h12
    | linear_combination h13
    | ring1
    | linear_combination (-m 2 0) * hA -
        (m 2 0 * m 0 1 * m 1 0 + m 2 1 * m 0 0 * m 1 0) * F4.two_eq_zero
    | linear_combination (-m 2 1) * hA -
        (m 2 0 * m 0 1 * m 1 1 + m 2 1 * m 0 1 * m 1 0) * F4.two_eq_zero
    | linear_combination (-m 3 0) * hA -
        (m 3 0 * m 0 1 * m 1 0 + m 3 1 * m 0 0 * m 1 0) * F4.two_eq_zero
    | linear_combination (-m 3 1) * hA -
        (m 3 0 * m 0 1 * m 1 1 + m 3 1 * m 0 1 * m 1 0) * F4.two_eq_zero

theorem eq_of_decomp_blocks {A B A' B' : SL(2, F4)} {y y' : SL(4, F4)} (hy : y ∈ YK)
    (hy' : y' ∈ YK)
    (h : y * (blockSL2 F4 3 0 A * blockSL2 F4 3 2 B) =
      y' * (blockSL2 F4 3 0 A' * blockSL2 F4 3 2 B')) :
    A = A' ∧ B = B' := by
  obtain ⟨a₂, a₄, a₅, a₈, rfl⟩ := hy
  obtain ⟨a₂', a₄', a₅', a₈', rfl⟩ := hy'
  have e00 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 0 0) h
  have e01 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 0 1) h
  have e10 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 1 0) h
  have e11 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 1 1) h
  have f22 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 2 2) h
  have f23 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 2 3) h
  have f32 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 3 2) h
  have f33 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 3 3) h
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_pSL, pMat, pb_blockSL2_zero, pb_blockSL2_two,
    Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e10 e11 f22 f23 f32 f33
  refine ⟨Subtype.ext (Matrix.ext fun i j => ?_), Subtype.ext (Matrix.ext fun i j => ?_)⟩
  · fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · exact e10
    · exact e11
  · fin_cases i <;> fin_cases j
    · exact f22
    · exact f23
    · exact f32
    · exact f33

theorem det_TL_of_involution {m : SL(4, F4)} (h02 : m 0 2 = 0) (h03 : m 0 3 = 0)
    (h12 : m 1 2 = 0) (h13 : m 1 3 = 0) (hm : m * m = 1) :
    m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
  have e00 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 0 0) hm
  have e01 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 0 1) hm
  have e10 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 1 0) hm
  have e11 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 1 1) hm
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]
    at e00 e01 e10 e11
  have hsq : (m 0 0 * m 1 1 - m 0 1 * m 1 0) * (m 0 0 * m 1 1 - m 0 1 * m 1 0) = 1 := by
    linear_combination (m 1 1 * m 1 1 + m 0 1 * m 1 0) * e00 + e11 -
      (m 1 0 * (m 0 0 + m 1 1)) * e01
  exact F4_mul_self_eq_one_imp _ hsq

theorem sigma_pairing {A B : SL(2, F4)} {y : SL(4, F4)} (hy : y ∈ YK)
    (hσ : sigmaSL F4 (y * (blockSL2 F4 3 0 A * blockSL2 F4 3 2 B)) =
      y * (blockSL2 F4 3 0 A * blockSL2 F4 3 2 B)) :
    blockSL2 F4 3 2 B = sigmaSL F4 (blockSL2 F4 3 0 A) := by
  have hmap := map_sigmaSL_range_zero F4
  have h1 : sigmaSL F4 (blockSL2 F4 3 0 A) ∈ (blockSL2 F4 3 2).range := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (sigmaSL F4).toMonoidHom (MonoidHom.mem_range.2 ⟨A, rfl⟩)
  obtain ⟨A', hA'⟩ := MonoidHom.mem_range.1 h1
  have h2 : blockSL2 F4 3 2 B ∈ (blockSL2 F4 3 0).range.map (sigmaSL F4).toMonoidHom := by
    rw [hmap]
    exact MonoidHom.mem_range.2 ⟨B, rfl⟩
  obtain ⟨x, hx, hxB⟩ := Subgroup.mem_map.1 h2
  obtain ⟨B', hB'⟩ := MonoidHom.mem_range.1 hx
  have hσB : sigmaSL F4 (blockSL2 F4 3 2 B) = blockSL2 F4 3 0 B' := by
    rw [hB', ← hxB]
    exact sigmaSL_sigmaSL _
  have key : sigmaSL F4 (y * (blockSL2 F4 3 0 A * blockSL2 F4 3 2 B)) =
      sigmaSL F4 y * (blockSL2 F4 3 0 B' * blockSL2 F4 3 2 A') := by
    rw [map_mul, map_mul, ← hA', hσB, blockSL2_comm B' A']
  have hσ2 : y * (blockSL2 F4 3 0 A * blockSL2 F4 3 2 B) =
      sigmaSL F4 y * (blockSL2 F4 3 0 B' * blockSL2 F4 3 2 A') := by
    rw [← key, hσ]
  have hAB : A' = B := (eq_of_decomp_blocks (sigmaSL_mem_YK hy) hy hσ2.symm).2
  rw [← hA', hAB]

theorem blockSL2_zero_mem_PK {A : SL(2, F4)} (h01 : A 0 1 = 0) (hAA : A * A = 1) :
    blockSL2 F4 3 0 A ∈ PK := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h := A.2
    rwa [Matrix.det_fin_two] at h
  have e00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    have h := congrArg (fun M : SL(2, F4) => (M : Matrix (Fin 2) (Fin 2) F4) 0 0) hAA
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using h
  have h00 : A 0 0 = 1 :=
    F4_mul_self_eq_one_imp _ (by linear_combination e00 - A 1 0 * h01)
  have h11 : A 1 1 = 1 := by linear_combination hdet - A 1 1 * h00 + A 1 0 * h01
  have heq : blockSL2 F4 3 0 A = pSL (A 1 0) 0 0 0 0 0 := by
    apply Subtype.ext
    rw [pb_blockSL2_zero, coe_pSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pMat, h00, h01, h11]
  rw [heq]
  exact pSL_mem_PK _ _ _ _ _ _

theorem exists_weyl_of_involution {g : SL(4, F4)} (hN : ∀ y ∈ YK, g * y * g⁻¹ ∈ YK)
    (hg2 : g * g = 1) (hσ : sigmaSL F4 g = g) (hP : g ∉ PK) :
    ∃ A : SL(2, F4), A 0 1 ≠ 0 ∧ A * A = 1 ∧ ∃ y ∈ YK,
      g = y * (blockSL2 F4 3 0 A * sigmaSL F4 (blockSL2 F4 3 0 A)) := by
  obtain ⟨h02, h03, h12, h13⟩ := YK_normalizer_zero hN
  have hdet := det_TL_of_involution h02 h03 h12 h13 hg2
  obtain ⟨A, B, y, hy, hA00, hA01, hA10, hA11, hdec⟩ :=
    exists_decomp_blocks h02 h03 h12 h13 hdet
  have hσ' : sigmaSL F4 (y * (blockSL2 F4 3 0 A * blockSL2 F4 3 2 B)) =
      y * (blockSL2 F4 3 0 A * blockSL2 F4 3 2 B) := by
    rw [← hdec]
    exact hσ
  have hB := sigma_pairing hy hσ'
  have hAA : A * A = 1 := by
    have e00 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 0 0) hg2
    have e01 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 0 1) hg2
    have e10 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 1 0) hg2
    have e11 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 1 1) hg2
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12,
      h13] at e00 e01 e10 e11
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hA00, hA01,
        hA10, hA11]
    all_goals first
      | linear_combination e00
      | linear_combination e01
      | linear_combination e10
      | linear_combination e11
  refine ⟨A, ?_, hAA, y, hy, ?_⟩
  · intro h01
    apply hP
    have hPK := blockSL2_zero_mem_PK h01 hAA
    rw [hdec, hB]
    exact PK.mul_mem (YK_le_PK hy) (PK.mul_mem hPK (sigmaSL_mem_PK hPK))
  · rw [hdec, hB]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow
