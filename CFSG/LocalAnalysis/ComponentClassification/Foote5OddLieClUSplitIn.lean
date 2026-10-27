module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUSplit
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUFam

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (signMat)

theorem ClU.uSplitInput (hgen : ClU.UBlockThreeGen) : ClU.USplitInput := by
  intro p f K _ h hp2 n hn hinj A l hl0 hlN hAA hns R hRodd hRi hRc
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := h.prime.two_le
    exact hp2 (by omega)
  set M := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hU : (M.map h.bar)ᵀ * M = 1 := (mem_uU h).1 A.2
  have hNi : h.bar l⁻¹ * l⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hlN, inv_one]
  have hU' : ((l⁻¹ • M).map h.bar)ᵀ * (l⁻¹ • M) = 1 := by
    rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, one_smul]
  have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form h h2 hU' hA'2
  set HG := uGL h Hm hHU with hHG
  have hHi : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Hm.map h.bar)ᵀ := rfl
  have hconj : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M *
      ((HG : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • signMat K J := by
    rw [hHi, coe_uGL]
    have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul]
  have hHH : Hm * (Hm.map h.bar)ᵀ = 1 := mul_eq_one_comm.1 hHU
  have hJ : ∃ a ∈ J, ∃ b, b ∉ J := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs, hsJ⟩ : ∃ s : K, s ≠ 0 ∧ signMat K J = s • 1 := by
      by_cases hne : J.Nonempty
      · obtain ⟨a, ha⟩ := hne
        refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
        ext i j
        simp [signMat, diagonal_apply, one_apply, hcon a ha i]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        refine ⟨1, one_ne_zero, ?_⟩
        ext i j
        simp [signMat, diagonal_apply, one_apply, hne]
    have e : l⁻¹ • M = s • 1 := by
      calc l⁻¹ • M = (l⁻¹ • M) * (Hm * (Hm.map h.bar)ᵀ) := by rw [hHH, Matrix.mul_one]
        _ = (Hm * signMat K J) * (Hm.map h.bar)ᵀ := by rw [← Matrix.mul_assoc, hHA]
        _ = s • 1 := by
            rw [hsJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
    apply hns (Units.mk0 (l * s) (mul_ne_zero hl0 hs))
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    change M = _
    have e2 : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e2, e, smul_smul, Matrix.smul_one_eq_diagonal]
    rfl
  obtain ⟨a, ha, b, hb⟩ := hJ
  refine commute_of_congr (uConjAut h (by omega) ⟨HG, uGL_mem h _ _⟩)⁻¹
    (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
  have hcg : MulAut.congr (uConjAut h (by omega) ⟨HG, uGL_mem h _ _⟩)⁻¹
      (uConjAut h (by omega) A) = uConjAut h (by omega) (uSign h J) := by
    rw [congr_eq_conj, inv_inv, ← map_inv, ← map_mul, ← map_mul]
    refine uConjAut_eq_of_eq_smul h hn hl0 ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
      coe_uSign]
    exact hconj
  rw [hcg] at hR'i hR'c
  intro r₁ h₁ r₂ h₂
  obtain ⟨α, β, hα, hβ, rfl⟩ := ClU.split_core h hgen hp2 hn hinj ha hb hR'odd hR'i hR'c h₁
  obtain ⟨α', β', hα', hβ', rfl⟩ := ClU.split_core h hgen hp2 hn hinj ha hb hR'odd hR'i hR'c h₂
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_uDiagJ, coe_uDiagJ,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs <;> ring

end CFSG.ComponentClassification.Foote5.OddLieCore
