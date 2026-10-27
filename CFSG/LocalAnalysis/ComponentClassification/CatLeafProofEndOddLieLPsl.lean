module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL2

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddLin

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.ComponentClassification.Burgoyne.PSL (coordBlock coordBlockEquiv
  isQuasisimple_coordBlock coordBlock_mono coordBlock_le_slCentralizer normalizes_coordBlock
  slCentralizer mem_slCentralizer signGL coe_signGL signMat exists_split_normal_form
  exists_quad_normal_form even_of_sq_eq_nonsquare quadMat quadPoly blockRep blockRep_injective
  exists_blockRep_of_commute blockRep_commute_quadMat blockSLE coe_blockSLE blockSLE_injective
  isQuasisimple_SL_quadExt QuadExt slReindex)
open CFSG.ComponentClassification.Burgoyne.C (coordBlockProjEquiv subsingleton_SL_of_le_one
  isSolvable_SL_two_of_card_three commutator_slCentralizer_le isSubnormal_map_mk
  le_map_commutator_of_perfect_mk)
open CFSG.ComponentClassification.CatLeafProof.EndOddCore
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K] [Finite K]


theorem false_of_config_psl (hK : ringChar K ≠ 2) (hn : 2 ≤ n) {x : projectiveSL n K}
    {L D : Subgroup (projectiveSL n K)} (h : Config x L D) : False := by
  obtain ⟨A, rfl⟩ := proj_surjective n K x
  have hx2 : proj n K (A * A) = 1 := by
    rw [map_mul, ← pow_two, ← h.twoComp.1, pow_orderOf_eq_one]
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hx2)
  have hAA : SpecialLinearGroup.toGL A * SpecialLinearGroup.toGL A =
      GeneralLinearGroup.scalar (Fin n) c := by
    apply Units.ext
    rw [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar,
      ← hc, Matrix.SpecialLinearGroup.coe_mul]
  have hns : ∀ c' : Kˣ, SpecialLinearGroup.toGL A ≠ GeneralLinearGroup.scalar (Fin n) c' := by
    intro c' hc'
    have hA : (A : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (c' : K) := by
      have := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc'
      simpa only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar]
        using this
    have hdet : c' ^ n = 1 := by
      apply Units.ext
      have := A.2
      rw [hA, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at this
      rw [Units.val_pow_eq_pow_val, this, Units.val_one]
    have h1 : proj n K A = 1 := proj_eq_one_iff.2 (mem_scalars.2 ⟨c', hdet, hA⟩)
    have := h.twoComp.1
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  by_cases hsq : IsSquare (c : K)
  ·
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by rw [hr, mul_zero])
    set μ := Units.mk0 r hr0
    have hAμ : SpecialLinearGroup.toGL A * SpecialLinearGroup.toGL A =
        GeneralLinearGroup.scalar (Fin n) (μ * μ) := by
      rw [hAA]
      congr 1
      exact Units.ext hr
    obtain ⟨H, J, a, b, ha, hb, hH⟩ := exists_split_normal_form hK hAμ hns
    have h' := h.map (conjAut n K H)
    rw [conjAut_proj] at h'
    refine false_of_config_psl_split hK ha hb (μ := μ) ?_ h'
    rw [toGL_slConjugation, hH]
  ·
    have hev := even_of_sq_eq_nonsquare hAA hsq
    obtain ⟨m', rfl⟩ : ∃ m', n = m' * 2 := ⟨n / 2, by obtain ⟨k, hk⟩ := hev; omega⟩
    have hAm : (SpecialLinearGroup.toGL A : Matrix (Fin (m' * 2)) (Fin (m' * 2)) K) *
        (SpecialLinearGroup.toGL A : Matrix (Fin (m' * 2)) (Fin (m' * 2)) K) = (c : K) • 1 := by
      have := congrArg Units.val hAA
      rw [Units.val_mul] at this
      rw [this]
      ext i j
      simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
    obtain ⟨H, hH⟩ := exists_quad_normal_form hsq hAm
    have h' := h.map (conjAut (m' * 2) K H)
    rw [conjAut_proj] at h'
    rcases (show m' = 1 ∨ 2 ≤ m' by omega) with rfl | hm
    · exact false_of_config_psl_nonsplit_one (by rw [coe_slConjugation]; exact hH) h'
    · exact false_of_config_psl_nonsplit hsq hm (by rw [coe_slConjugation]; exact hH) h'

end CFSG.ComponentClassification.CatLeafProof.EndOddLin
