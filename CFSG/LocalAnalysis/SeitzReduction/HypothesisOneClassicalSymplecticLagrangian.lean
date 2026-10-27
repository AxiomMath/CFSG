module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticLagrangianCases

public section

namespace CFSG.SeitzReduction

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open SymplecticTorusWeyl (leviSp coe_leviSp)
open LinearMap (BilinForm)

namespace SymplecticLagrangian

variable {r : ℕ} {K : Type} [Field K]

theorem isTotallyIsotropic_and_finrank_of_eq_orthogonal {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : W = (pairedSympForm K r).orthogonal W) :
    IsTotallyIsotropic (pairedSympForm K r) W ∧ Module.finrank K W = r := by
  refine ⟨fun x hx y hy => ?_, ?_⟩
  · rw [hW] at hy
    exact BilinForm.mem_orthogonal_iff.mp hy x hx
  · have h := BilinForm.finrank_add_finrank_orthogonal SymplecticFlag.pairedSympForm_isAlt.isRefl W
    rw [BilinForm.orthogonal_top_eq_bot SymplecticFlag.pairedSympForm_nondegenerate, inf_bot_eq,
      finrank_bot,
      add_zero, ← hW, finrank_standard] at h
    omega

theorem orthogonal_isoFlag_self :
    (pairedSympForm K r).orthogonal (isoFlag r K r) = isoFlag r K r := by
  ext v
  rw [mem_orthogonal_isoFlag, mem_isoFlag]
  constructor
  · intro h
    exact ⟨fun j => h j j.2, fun j hj => absurd j.2 (not_lt.mpr hj)⟩
  · intro h j _
    exact h.1 j

theorem transpose_eq_of_fromBlocks_mem {S : Matrix (Fin r) (Fin r) K}
    (h : (fromBlocks 1 S 0 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      fromBlocks 0 1 (-1) 0 * fromBlocks 1 S 0 1 = fromBlocks 0 1 (-1) 0) : Sᵀ = S := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  simp only [transpose_one, transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul] at h
  have h4 := h.2.2.2
  rw [neg_add_eq_zero] at h4
  exact h4.symm

theorem exists_eq_conj_upperUnipotentSp {s : StatedSp r K} (hs : s * s = 1)
    (hW : displacement s = (pairedSympForm K r).orthogonal (displacement s)) :
    ∃ (g : StatedSp r K) (S : Matrix (Fin r) (Fin r) K) (hS : Sᵀ = S),
      IsUnit S ∧ s = g * upperUnipotentSp r K hS * g⁻¹ := by
  obtain ⟨hiso, hdim⟩ := isTotallyIsotropic_and_finrank_of_eq_orthogonal hW
  obtain ⟨hiso₀, hdim₀⟩ :=
    isTotallyIsotropic_and_finrank_of_eq_orthogonal (orthogonal_isoFlag_self (K := K) (r := r)).symm
  obtain ⟨g, hg⟩ := exists_statedSp_map_eq hiso₀ hiso (hdim₀.trans hdim.symm)
  set s₁ := g⁻¹ * s * g with hs₁
  have hmap : ∀ x ∈ isoFlag r K r, spMat g *ᵥ x ∈ displacement s := fun x hx => by
    rw [← hg]
    exact Submodule.mem_map_of_mem hx
  have hfix : ∀ x ∈ isoFlag r K r, spMat s₁ *ᵥ x = x := by
    intro x hx
    have hgx := hmap x hx
    rw [hW] at hgx
    have h0 := displacement_eq_zero_of_mem_orthogonal hs hgx
    rw [hs₁, spMat_mul_mulVec, spMat_mul_mulVec, sub_eq_zero.mp h0, spMat_inv_mulVec_mulVec]
  have hgs : ∀ v, spMat g *ᵥ (spMat s₁ *ᵥ v - v) = spMat s *ᵥ (spMat g *ᵥ v) - spMat g *ᵥ v := by
    intro v
    rw [hs₁, mulVec_sub, spMat_mul_mulVec, spMat_mul_mulVec, spMat_mulVec_inv_mulVec]
  have hdisp : ∀ v, spMat s₁ *ᵥ v - v ∈ isoFlag r K r := by
    intro v
    have h1 : spMat s *ᵥ (spMat g *ᵥ v) - spMat g *ᵥ v ∈ displacement s :=
      mem_displacement.mpr ⟨_, rfl⟩
    rw [← hg] at h1
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp h1
    have hwe' : spMat g *ᵥ w = spMat g *ᵥ (spMat s₁ *ᵥ v - v) := by
      rw [hgs]
      exact hwe
    have hinj : w = spMat s₁ *ᵥ v - v := by
      have := congrArg (spMat g⁻¹ *ᵥ ·) hwe'
      simpa only [spMat_inv_mulVec_mulVec] using this
    rw [← hinj]
    exact hw
  set S := (spMat s₁).toBlocks₁₂ with hSdef
  have hblock : spMat s₁ = fromBlocks 1 S 0 1 := by
    have hcol : ∀ j k, spMat s₁ k j = (spMat s₁ *ᵥ Pi.single j 1) k := fun j k => by
      rw [mulVec_single_one]
      rfl
    have hsingle : ∀ j : Fin r, (Pi.single (Sum.inl j) 1 : Fin r ⊕ Fin r → K) ∈ isoFlag r K r :=
      fun j => mem_isoFlag.mpr ⟨fun i => by simp, fun i hi => absurd i.2 (not_lt.mpr hi)⟩
    ext (i | i) (j | j)
    · rw [hcol, hfix _ (hsingle j)]
      simp [Matrix.one_apply, Pi.single_apply]
    · rfl
    · rw [hcol, hfix _ (hsingle j)]
      simp
    · have h := (mem_isoFlag.mp (hdisp (Pi.single (Sum.inr j) 1))).1 i
      rw [Pi.sub_apply, ← hcol, sub_eq_zero] at h
      rw [h]
      simp [Matrix.one_apply, Pi.single_apply]
  have hS : Sᵀ = S := by
    have h := SymplecticTorusWeyl.mem_statedSp_iff.mp s₁.2
    change (spMat s₁)ᵀ * fromBlocks 0 1 (-1) 0 * spMat s₁ = fromBlocks 0 1 (-1) 0 at h
    rw [hblock] at h
    exact transpose_eq_of_fromBlocks_mem h
  have hSu : IsUnit S := by
    refine Matrix.mulVec_surjective_iff_isUnit.mp fun y => ?_
    have hy : (Sum.elim y 0 : Fin r ⊕ Fin r → K) ∈ isoFlag r K r :=
      mem_isoFlag.mpr ⟨fun i => rfl, fun i hi => absurd i.2 (not_lt.mpr hi)⟩
    obtain ⟨v', hv'⟩ := mem_displacement.mp (hmap _ hy)
    set v := spMat g⁻¹ *ᵥ v' with hv
    have h1 : spMat s₁ *ᵥ v - v = Sum.elim y 0 := by
      have h2 := hgs v
      rw [hv, spMat_mulVec_inv_mulVec, hv'] at h2
      have := congrArg (spMat g⁻¹ *ᵥ ·) h2
      simpa only [spMat_inv_mulVec_mulVec] using this
    refine ⟨fun j => v (Sum.inr j), funext fun i => ?_⟩
    have h3 := congrFun h1 (Sum.inl i)
    rw [hblock, Pi.sub_apply, fromBlocks_mulVec, Sum.elim_inl, Sum.elim_inl, one_mulVec,
      Pi.add_apply] at h3
    simp only [Function.comp_apply, add_sub_cancel_left] at h3
    exact h3
  refine ⟨g, S, hS, hSu, ?_⟩
  have hs₁' : s₁ = upperUnipotentSp r K hS := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [coe_upperUnipotentSp]
    exact hblock
  rw [← hs₁', hs₁]
  group

theorem exists_mul_mul_transpose_eq_one [Finite K] [CharP K 2] {S : Matrix (Fin r) (Fin r) K}
    (hS : Sᵀ = S) (hSu : IsUnit S) (halt : ¬∀ x : Fin r → K, x ⬝ᵥ (S *ᵥ x) = 0) :
    ∃ P : GL (Fin r) K,
      (P : Matrix (Fin r) (Fin r) K) * S * (P : Matrix (Fin r) (Fin r) K)ᵀ = 1 := by
  have hsq : ∀ a : K, IsSquare a := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
  have hBsymm : (Matrix.toBilin' S).IsSymm := ⟨fun v w => by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_mulVec, ← mulVec_transpose,
      hS, dotProduct_comm]⟩
  have hBnd : (Matrix.toBilin' S).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_of_det_ne_zero
      ((Matrix.isUnit_iff_isUnit_det _).mp hSu).ne_zero)
  push Not at halt
  obtain ⟨x, hx⟩ := halt
  obtain ⟨b, hb⟩ := UnitaryHigher.exists_orthonormal_basis_of_charTwo hsq hBsymm hBnd
    (Or.inr ⟨x, by rw [Matrix.toBilin'_apply']; exact hx⟩)
  set b' := b.reindex (finCongr (Module.finrank_fin_fun K)) with hb'
  set Q := (Pi.basisFun K (Fin r)).toMatrix b' with hQ
  have hQS : Qᵀ * S * Q = 1 := by
    have h := BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K (Fin r)) b' (Matrix.toBilin' S)
    rw [BilinForm.toMatrix_basisFun, BilinForm.toMatrix'_toBilin'] at h
    rw [h]
    ext i j
    rw [BilinForm.toMatrix_apply, hb', Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb,
      Matrix.one_apply]
    simp only [(finCongr (Module.finrank_fin_fun K)).symm.injective.eq_iff]
  have hQu : IsUnit Q :=
    IsUnit.of_mul_eq_one _ (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  have hQtu : IsUnit Qᵀ := (Matrix.isUnit_transpose Q).mpr hQu
  refine ⟨hQtu.unit, ?_⟩
  rw [IsUnit.unit_spec, transpose_transpose]
  exact hQS

end SymplecticLagrangian

open SymplecticLagrangian

theorem involutionCriterion_spInner_of_eq {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hr : 3 ≤ r) {s : StatedSp r K} (hs : s * s = 1)
    (hW : displacement s = (pairedSympForm K r).orthogonal (displacement s)) :
    InvolutionCriterion (spInner r K s) := by
  have hconj : ∀ h t : StatedSp r K, InvolutionCriterion (spInner r K t) →
      InvolutionCriterion (spInner r K (h * t * h⁻¹)) := by
    intro h t ht
    have := ht.conj (spInner r K h)
    rwa [← map_inv, ← map_mul, ← map_mul] at this
  obtain ⟨g, S, hS, hSu, rfl⟩ := exists_eq_conj_upperUnipotentSp hs hW
  apply hconj
  by_cases halt : ∀ x : Fin r → K, x ⬝ᵥ (S *ᵥ x) = 0
  · exact involutionCriterion_upperUnipotentSp_of_isAlt hr hS hSu halt
  · obtain ⟨P, hP⟩ := exists_mul_mul_transpose_eq_one hS hSu halt
    have h1 : leviSp P * upperUnipotentSp r K hS * (leviSp P)⁻¹ =
        upperUnipotentSp r K (transpose_one : (1 : Matrix (Fin r) (Fin r) K)ᵀ = 1) := by
      rw [leviSp_conj_upperUnipotentSp]
      exact upperUnipotentSp_eq_of_eq _ _ hP
    have h2 : upperUnipotentSp r K hS = (leviSp P)⁻¹ *
        upperUnipotentSp r K (transpose_one : (1 : Matrix (Fin r) (Fin r) K)ᵀ = 1) *
          ((leviSp P)⁻¹)⁻¹ := by
      rw [← h1]
      group
    rw [h2]
    apply hconj
    rcases Nat.even_or_odd r with heven | hodd
    · exact involutionCriterion_upperUnipotentSp_one_of_even hr heven
    · exact involutionCriterion_upperUnipotentSp_one_of_odd hr hodd

end CFSG.SeitzReduction
