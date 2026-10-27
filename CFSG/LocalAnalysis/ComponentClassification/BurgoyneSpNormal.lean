module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelfE

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (eigenPlus eigenMinus invSMulOp
  exists_bilin_paired_equiv)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

@[expose] def colMat (u : Fin r ⊕ Fin r → Fin r ⊕ Fin r → K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  Matrix.of fun x c => u c x

theorem gram_colMat (u : Fin r ⊕ Fin r → Fin r ⊕ Fin r → K) (p q : Fin r ⊕ Fin r) :
    ((colMat u)ᵀ * formJ r K * colMat u) p q = pairedSympForm K r (u p) (u q) := by
  rw [pairedSympForm_eq, dotProduct, Matrix.mul_apply]
  simp only [Matrix.mul_apply, transpose_apply, colMat, Matrix.of_apply, mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem exists_sp_of_gram {u : Fin r ⊕ Fin r → Fin r ⊕ Fin r → K}
    (h : ∀ p q, pairedSympForm K r (u p) (u q) = formJ r K p q) :
    ∃ H : StatedSp r K, ((H : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = colMat u := by
  have hG : (colMat u)ᵀ * formJ r K * colMat u = formJ r K := by
    ext p q
    rw [gram_colMat, h]
  have hJ : (formJ r K).det ≠ 0 := by
    have hJJ : formJ r K * formJ r K = -1 := by
      rw [formJ, fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg]
      rw [← fromBlocks_one, fromBlocks_neg, neg_zero]
    intro h0
    have := congrArg Matrix.det hJJ
    rw [det_mul, h0, zero_mul, det_neg, det_one, mul_one] at this
    exact (neg_one_pow_ne_zero (Fintype.card (Fin r ⊕ Fin r))) this.symm
  have hdet : IsUnit (colMat u).det := by
    have := congrArg Matrix.det hG
    rw [det_mul, det_mul, det_transpose] at this
    have h3 : (colMat u).det * (colMat u).det = 1 := by
      have h4 : ((colMat u).det * (colMat u).det - 1) * (formJ r K).det = 0 := by
        linear_combination this
      exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_right hJ)
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul] at h3
    exact zero_ne_one h3
  refine ⟨⟨Matrix.nonsingInvUnit _ hdet, mem_statedSp_iff.2 ?_⟩, rfl⟩
  exact hG

theorem inv_mul_mul_eq_of_cols {u : Fin r ⊕ Fin r → Fin r ⊕ Fin r → K} {H : GL (Fin r ⊕ Fin r) K}
    (hH : (H : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = colMat u)
    {A A' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h : ∀ c, A *ᵥ u c = ∑ d, A' d c • u d) :
    ((H⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * A *
      (H : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = A' := by
  have hAH : A * (H : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (H : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * A' := by
    rw [hH]
    ext x c
    have h1 := congrFun (h c) x
    have e1 : (A * colMat u) x c = (A *ᵥ u c) x := by
      simp [Matrix.mul_apply, colMat, mulVec, dotProduct]
    have e2 : (colMat u * A') x c = (∑ d, A' d c • u d) x := by
      simp [Matrix.mul_apply, colMat, Finset.sum_apply, mul_comm]
    rw [e1, e2, h1]
  rw [Matrix.mul_assoc, hAH, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

theorem sum_diagonal_smul (w : Fin r ⊕ Fin r → K) (u : Fin r ⊕ Fin r → Fin r ⊕ Fin r → K)
    (c : Fin r ⊕ Fin r) : ∑ d, diagonal w d c • u d = w c • u c := by
  rw [Finset.sum_eq_single c (fun d _ hd => by rw [diagonal_apply_ne _ hd, zero_smul])
    (by simp), diagonal_apply_eq]

abbrev stdSkew (r : ℕ) (K : Type) [Field K] : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  diagonal (Sum.elim (fun _ => 1) fun _ => -1)

theorem exists_skew_split_normal_form (hK : ringChar K ≠ 2) {A : gsp r K} {l : K} (hl0 : l ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (l ^ 2) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (-(l ^ 2)) • formJ r K) :
    ∃ H : StatedSp r K, ((((H : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((H : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        l • stdSkew r K := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAA' := linA_mul_self hAA
  have hTB : ∀ v w, pairedSympForm K r (invSMulOp l ((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (invSMulOp l ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = -pairedSympForm K r v w := by
    intro v w
    simp only [invSMulOp, LinearMap.smul_apply, linA_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [form_similitude hJ]
    field_simp
  obtain ⟨hisoP, hisoM, -, hdim2, -, hpairMP, -⟩ := exists_bilin_paired_equiv h2
    pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate hl0 hAA' hTB
  rw [finrank_standard] at hdim2
  have hfinP : Module.finrank K (VPl A l) = r := by
    show Module.finrank K (eigenPlus l _) = r
    omega
  have hfinM : Module.finrank K (VMl A l) = r := by
    have := (exists_bilin_paired_equiv h2 pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate hl0 hAA' hTB).2.2.1
    show Module.finrank K (eigenMinus l _) = r
    omega
  set bP := Module.finBasisOfFinrankEq K (VPl A l) hfinP with hbP
  set φ : VMl A l →ₗ[K] Module.Dual K (VPl A l) :=
    (LinearMap.lcomp K K (VPl A l).subtype).comp (LinearMap.comp
      (LinearMap.flip (pairedSympForm K r)) (VMl A l).subtype) with hφ
  have hφapp : ∀ (w : VMl A l) (v : VPl A l), φ w v = pairedSympForm K r v w := fun w v => by
    rw [hφ]
    rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    rw [Submodule.mem_bot]
    exact Subtype.ext (hpairMP w w.2 fun v hv => by
      have := congrArg (fun f : Module.Dual K (VPl A l) => f ⟨v, hv⟩) hw
      simpa [hφapp] using this)
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hinj
    · rw [Subspace.dual_finrank_eq, hfinP, hfinM]
  set eφ := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩ with heφ
  set fM : Fin r → VMl A l := fun j => eφ.symm (bP.coord j) with hfM
  have hBf : ∀ i j, pairedSympForm K r (bP i) (fM j) = if j = i then 1 else 0 := by
    intro i j
    have h1 : φ (fM j) = bP.coord j := by
      rw [hfM]
      exact eφ.apply_symm_apply (bP.coord j)
    rw [← hφapp, h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  set u : Fin r ⊕ Fin r → Fin r ⊕ Fin r → K :=
    Sum.elim (fun i => ((bP i : VPl A l) : Fin r ⊕ Fin r → K))
      (fun j => ((fM j : VMl A l) : Fin r ⊕ Fin r → K)) with hu
  have hgram : ∀ p q, pairedSympForm K r (u p) (u q) = formJ r K p q := by
    rintro (i | i) (j | j)
    · simp only [hu, Sum.elim_inl, formJ, fromBlocks_apply₁₁, Matrix.zero_apply]
      exact hisoP _ (bP i).2 _ (bP j).2
    · simp only [hu, Sum.elim_inl, Sum.elim_inr, formJ, fromBlocks_apply₁₂, one_apply]
      rw [hBf]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    · simp only [hu, Sum.elim_inl, Sum.elim_inr, formJ, fromBlocks_apply₂₁, Matrix.neg_apply,
        one_apply]
      rw [← bJ_eq, bJ_swap, bJ_eq, hBf]
    · simp only [hu, Sum.elim_inr, formJ, fromBlocks_apply₂₂, Matrix.zero_apply]
      exact hisoM _ (fM i).2 _ (fM j).2
  obtain ⟨H, hH⟩ := exists_sp_of_gram hgram
  refine ⟨H, inv_mul_mul_eq_of_cols hH fun c => ?_⟩
  have hls : l • stdSkew r K = diagonal (l • Sum.elim (fun _ => (1 : K)) fun _ => -1) := by
    rw [stdSkew, ← diagonal_smul]
  rw [hls, sum_diagonal_smul]
  rcases c with i | j
  · simp only [hu, Sum.elim_inl, Pi.smul_apply, smul_eq_mul, mul_one]
    exact (mem_eigenPlus hl0).1 (bP i).2
  · simp only [hu, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, mul_neg, mul_one]
    exact (mem_eigenMinus hl0).1 (fM j).2

end CFSG.ComponentClassification.Burgoyne.Sp
