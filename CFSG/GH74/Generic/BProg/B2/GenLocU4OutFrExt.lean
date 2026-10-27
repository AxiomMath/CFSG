module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrame
import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtBlock
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutNF
import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtFrame

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.Generic.S1.Uni Matrix

namespace GenLocU4OutFrExt

section Helpers

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def extT (l i : K) : Matrix (Fin 4) (Fin 4) K :=
  !![l, -(l * i), 0, 0; 0, 0, l, -(l * i); l, l * i, 0, 0; 0, 0, l, l * i]

theorem ext_unit (h : UnitaryFieldData p f K) (l i : K) (hl : 2 * h.bar l * l = 1)
    (hi : i * i = -1) (hbi : h.bar i = i) :
    cT h (extT l i) * (L5U5.wMat : Matrix (Fin 4) (Fin 4) K) * extT l i = 1 := by
  rw [GenLocU4OutFrame.wMat_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [extT, cT, Matrix.mul_apply, Fin.sum_univ_four, hbi] <;>
    first | linear_combination hl | linear_combination hl + (-2 * h.bar l * l) * hi

theorem ext_intertwine (l i : K) (hi : i * i = -1) :
    Matrix.diagonal ![i, i, -i, -i] * extT l i =
      extT l i * (GenLocU4Out.xi : Matrix (Fin 4) (Fin 4) K) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [extT, GenLocU4Out.xi, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal] <;>
    first | ring1 | linear_combination (-l) * hi

theorem blk4_neg_one_eq_diag :
    blk4 (1 : Matrix (Fin 2) (Fin 2) K) (-1) = Matrix.diagonal ![1, 1, -1, -1] := by
  rw [← GenLocU4OutFrame.blk4_eq_diag, neg_one_smul]

end Helpers

theorem exists_ext_frame {p f : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {x : Matrix (Fin 4) (Fin 4) K}
    (hx : CFSG.GH74.Generic.BProg.B2.GenLocU4Basic.IsUnitaryU (p ^ f) x) (hx2 : x * x = -1) :
    ∃ U : Matrix (Fin 4) (Fin 4) K,
      CFSG.GH74.Generic.BProg.B2.GenLocU4Basic.IsUnitaryU (p ^ f) U ∧
      x * U = U * (CFSG.GH74.Generic.BProg.B2.GenLocU4Out.xi : Matrix (Fin 4) (Fin 4) K) := by
  classical
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  obtain ⟨i, hi⟩ : ∃ i : K, i * i = -1 := by
    have := Fintype.ofFinite K
    have h4 : Fintype.card K % 4 ≠ 3 := by
      rw [← Nat.card_eq_fintype_card, hK, Nat.pow_mod, hq]
      norm_num
    obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.2 h4
    exact ⟨r, hr.symm⟩
  have hbi : h.bar i = i := by
    rw [UnitaryFieldData.bar_apply]
    exact GenLocU4ExtBlock.pow_eq_self_of_sq_neg_one hq hi
  have hxc : cT h x = -x := by
    have hu : cT h x * x = 1 := (GenLocU4OutFrame.isUnitaryU_iff_cT h x).1 hx
    calc cT h x = cT h x * (x * (-x)) := by rw [Matrix.mul_neg, hx2, neg_neg, Matrix.mul_one]
      _ = (cT h x * x) * (-x) := (Matrix.mul_assoc _ _ _).symm
      _ = -x := by rw [hu, Matrix.one_mul]
  have hii : (-i) * (-i) = -1 := by linear_combination hi
  have hBB : ((-i) • x) * ((-i) • x) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hii, hx2]
    simp
  have hBu : cT h ((-i) • x) * ((-i) • x) = -1 := by
    have hbar : h.bar (-i) = -i := by rw [map_neg, hbi]
    rw [cT_smul, hbar, hxc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hii, Matrix.neg_mul, hx2]
    simp
  obtain ⟨P, hPw, hBP⟩ := exists_paired_basis h hp2 hBB hBu
  rw [blk4_neg_one_eq_diag] at hBP
  have hxP : x * (P : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![i, i, -i, -i] := by
    have e1 : x = i • ((-i) • x) := by
      rw [smul_smul]
      have : i * (-i) = 1 := by linear_combination -hi
      rw [this, one_smul]
    have e2 : i • (Matrix.diagonal ![1, 1, -1, -1] : Matrix (Fin 4) (Fin 4) K) =
        Matrix.diagonal ![i, i, -i, -i] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.diagonal]
    rw [e1, Matrix.smul_mul, hBP, ← Matrix.mul_smul, e2]
  have hbar2 : h.bar (2 : K)⁻¹ = (2 : K)⁻¹ := by
    rw [map_inv₀]; congr 1; exact map_ofNat h.bar 2
  obtain ⟨l, hl⟩ := GenLocU4OutFrame.exists_two_inv_norm h (2 : K)⁻¹ hbar2 (inv_ne_zero h2)
  have hl' : 2 * h.bar l * l = 1 := by
    calc 2 * h.bar l * l = 2 * (h.bar l * l) := by ring
      _ = 1 := by rw [hl]; exact mul_inv_cancel₀ h2
  refine ⟨(P : Matrix (Fin 4) (Fin 4) K) * extT l i, ?_, ?_⟩
  · rw [GenLocU4OutFrame.isUnitaryU_iff_cT h]
    have e1 : cT h ((P : Matrix (Fin 4) (Fin 4) K) * extT l i) *
        ((P : Matrix (Fin 4) (Fin 4) K) * extT l i) =
        cT h (extT l i) * (cT h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K)) *
          extT l i := by
      rw [cT_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, hPw]
    exact ext_unit h l i hl' hi hbi
  · rw [← Matrix.mul_assoc, hxP, Matrix.mul_assoc, ext_intertwine l i hi, ← Matrix.mul_assoc]

end GenLocU4OutFrExt

end CFSG.GH74.Generic.BProg.B2
