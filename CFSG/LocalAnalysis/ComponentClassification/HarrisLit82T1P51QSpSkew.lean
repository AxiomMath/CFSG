module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSplit
public import CFSG.Assembly.RankThreeEvenDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.Burgoyne.PSL (eq_scalar_of_commute_single)

variable {r : ℕ} {K : Type} [Field K]

theorem norm_eq_one_of_rot_mem [NeZero r] {A' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hA'J : A'ᵀ * formJ r K * A' = formJ r K) (hA'2 : A' * A' = -1) {x y : K}
    (hD : (x • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + y • A')ᵀ * formJ r K *
      (x • 1 + y • A') = formJ r K) : x ^ 2 + y ^ 2 = 1 := by
  have hAJ : A'ᵀ * formJ r K = -(formJ r K * A') := by
    calc A'ᵀ * formJ r K = A'ᵀ * formJ r K * (A' * -A') := by
          rw [Matrix.mul_neg, hA'2, neg_neg, Matrix.mul_one]
      _ = -(A'ᵀ * formJ r K * A' * A') := by
          rw [Matrix.mul_neg, Matrix.mul_neg, ← Matrix.mul_assoc]
      _ = -(formJ r K * A') := by rw [hA'J]
  have e : (x • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + y • A')ᵀ * formJ r K *
      (x • 1 + y • A') = (x ^ 2 + y ^ 2) • formJ r K := by
    rw [transpose_add, transpose_smul, transpose_smul, transpose_one]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hAJ]
    rw [Matrix.neg_mul, Matrix.mul_assoc, hA'2, Matrix.mul_neg, Matrix.mul_one, neg_neg]
    module
  rw [e] at hD
  exact smul_formJ_injective r (by rw [hD, one_smul])

theorem rot_of_commute_levN (h2 : (2 : K) ≠ 0) (hr : 1 ≤ r) {l : K} (hl0 : l ≠ 0)
    {D : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hDA : D * stdSkew r K = stdSkew r K * D)
    (hDL : ∀ i j : Fin r, i ≠ j → D * levN i j = levN i j * D) :
    ∃ x y : K, D = x • 1 + y • (l • stdSkew r K) := by
  have hblk := fromBlocks_of_commute_stdSkew h2 hDA
  set P := D.toBlocks₁₁ with hP
  set R := D.toBlocks₂₂ with hR
  have hPc : ∀ i j : Fin r, i ≠ j → P * single i j 1 = single i j 1 * P := by
    intro i j hij
    have h := hDL i j hij
    rw [hblk, levN, fromBlocks_multiply, fromBlocks_multiply] at h
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
    exact (Matrix.fromBlocks_inj.1 h).1
  have hRc : ∀ i j : Fin r, i ≠ j → R * single i j 1 = single i j 1 * R := by
    intro i j hij
    have h := hDL j i (Ne.symm hij)
    rw [hblk, levN, fromBlocks_multiply, fromBlocks_multiply] at h
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul] at h
    exact neg_inj.1 (Matrix.fromBlocks_inj.1 h).2.2.2
  have ha := eq_scalar_of_commute_single ⟨0, by omega⟩ hPc
  have hb := eq_scalar_of_commute_single ⟨0, by omega⟩ hRc
  set a := P ⟨0, by omega⟩ ⟨0, by omega⟩
  set b := R ⟨0, by omega⟩ ⟨0, by omega⟩
  refine ⟨(a + b) / 2, (a - b) / (2 * l), ?_⟩
  rw [hblk, ha, hb]
  ext (i | i) (j | j) <;> by_cases hij : i = j <;>
    simp [stdSkew, scalar_apply, one_apply, hij, Matrix.smul_apply] <;>
    field_simp <;> ring

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
