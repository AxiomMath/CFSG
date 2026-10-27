module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL4

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddLin

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.C (uBlockProjEquiv subsingleton_statedSU_of_le_one
  statedSUCongr uBlock_mono isSolvable_SL_two_of_card_three commutator_le_uBlock_sup
  isSubnormal_map_mk le_map_commutator_of_perfect_mk)
open CFSG.ComponentClassification.Burgoyne.PSL (signMat compInd)
open CFSG.ComponentClassification.CatLeafProof.EndOddCore
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

variable [Finite K]

theorem false_of_config_psu (hu : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {x : StatedProj (StatedSU n (p ^ f) K)} {L D : Subgroup (StatedProj (StatedSU n (p ^ f) K))}
    (h : Config x L D) : False := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have h2 := two_ne_zero_of_unitary hu hp2
  obtain ⟨F, _, _, hF, ⟨e₂⟩⟩ := Burgoyne.C.exists_statedSU_two_equiv hu
  obtain ⟨A, rfl⟩ := projH_surjective x
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hU : (Am.map hu.bar)ᵀ * Am = 1 := ((mem_unitarySU_iff hu).1 A.2).2
  have hx2 : projH _ (A * A) = 1 := by
    rw [map_mul, ← pow_two, ← h.twoComp.1, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).1 hx2
  have hAA : Am * Am = (c : K) • 1 := by
    have e : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Am * Am := by
      rw [hc]
      rfl
    rw [← e, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hN : hu.norm (c : K) = 1 := by
    have e : ((Am * Am).map hu.bar)ᵀ * (Am * Am) = 1 := by
      rw [Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ Am Am, hU,
        Matrix.one_mul, hU]
    rw [hAA] at e
    have e1 := congrFun (congrFun e ⟨0, by omega⟩) ⟨0, by omega⟩
    simp [Matrix.mul_apply, Matrix.one_apply] at e1
    rw [UnitaryFieldData.norm, mul_comm]
    simpa [Matrix.smul_apply, Matrix.one_apply] using e1
  obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one hu hp2 hN
  have hAA' : Am * Am = (l ^ 2) • 1 := by rw [hAA, hlc]
  have hNl : hu.norm l * hu.norm l = 1 := by
    rw [← hN, ← hlc, UnitaryFieldData.norm, UnitaryFieldData.norm, map_pow]
    ring
  have hA'2 : (l⁻¹ • Am) * (l⁻¹ • Am) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  have hmap : (l⁻¹ • Am).map hu.bar = hu.bar l⁻¹ • Am.map hu.bar := by
    ext i j
    simp [map_mul]
  have he : Am = l • (l⁻¹ • Am) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
  have htr : ∀ {Hm : Matrix (Fin n) (Fin n) K} (hHU : (Hm.map hu.bar)ᵀ * Hm = 1),
      ∃ L' D' : Subgroup (StatedProj (StatedSU n (p ^ f) K)),
        Config (projH _ (⟨(uGL hu Hm hHU)⁻¹ * A * (uGL hu Hm hHU)⁻¹⁻¹,
          uConjSU_mem hu ⟨_, inv_mem (uGL_mem hu Hm hHU)⟩ A⟩ : StatedSU n (p ^ f) K)) L' D' := by
    intro Hm hHU
    have := h.map (uConjAut hu (by omega) ⟨_, inv_mem (uGL_mem hu Hm hHU)⟩)
    rw [uConjAut_proj] at this
    exact ⟨_, _, this⟩
  rcases mul_self_eq_one_iff.1 hNl with hN1 | hN1
  ·
    have hNi : hu.bar l⁻¹ * l⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN1, inv_one]
    have hU' : ((l⁻¹ • Am).map hu.bar)ᵀ * (l⁻¹ • Am) = 1 := by
      rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, one_smul]
    obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form hu h2 hU' hA'2
    have hconj : (Hm.map hu.bar)ᵀ * Am * Hm = l • signMat K J := by
      rw [he, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
        Matrix.one_mul]
    have hHH : Hm * (Hm.map hu.bar)ᵀ = 1 := mul_eq_one_comm.1 hHU
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
      have e : Am = (l * s) • 1 := by
        calc Am = Hm * ((Hm.map hu.bar)ᵀ * Am * Hm) * (Hm.map hu.bar)ᵀ := by
              simp only [← Matrix.mul_assoc, hHH, Matrix.one_mul]
              rw [Matrix.mul_assoc, hHH, Matrix.mul_one]
          _ = (l * s) • 1 := by
              rw [hconj, hsJ, smul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
      have hsc : A ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) := by
        refine ⟨Units.mk0 (l * s) (mul_ne_zero hl0 hs), Units.ext ?_⟩
        rw [GeneralLinearGroup.coe_scalar]
        change _ = Am
        rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
        rfl
      have h1 : projH (StatedSU n (p ^ f) K) A = 1 := (QuotientGroup.eq_one_iff _).2 hsc
      have := h.twoComp.1
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    obtain ⟨a, ha, b, hb⟩ := hJ
    obtain ⟨L', D', hC'⟩ := htr hHU
    refine false_of_config_psu_split hu hp2 hF e₂ ha hb hl0 ?_ hC'
    change (Hm.map hu.bar)ᵀ * Am * Hm = _
    exact hconj
  ·
    have hNi : hu.bar l⁻¹ * l⁻¹ = -1 := by
      rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN1, inv_neg, inv_one]
    have hU' : ((l⁻¹ • Am).map hu.bar)ᵀ * (l⁻¹ • Am) = -1 := by
      rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi,
        neg_one_smul]
    obtain ⟨m', rfl⟩ := exists_half_of_antiunitary hu h2 hU' hA'2
    have hm : 2 ≤ m' := by omega
    obtain ⟨Hm, hHU, hHA⟩ := exists_paired_unitary_normal_form hu h2 hU' hA'2 hl0 hN1
    obtain ⟨L', D', hC'⟩ := htr hHU
    refine false_of_config_psu_paired hu hp2 hm hl0 hN1 ?_ hC'
    change (Hm.map hu.bar)ᵀ * Am * Hm = _
    rw [he, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul, prA, ← map_smul, fromBlocks_smul]
    congr 2
    · rw [smul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    · rw [smul_smul, ← sq]
    · rw [smul_zero]

end CFSG.ComponentClassification.CatLeafProof.EndOddLin
