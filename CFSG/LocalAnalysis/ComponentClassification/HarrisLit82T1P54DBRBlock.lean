module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBBlock

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup Matrix Assembly.LowTwoRank

variable {K : Type} [Field K]

section Block

variable {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  {Q₁ : (ι₁ → K) → K} {Q₂ : (ι₂ → K) → K}

theorem toBlocks_eq_zero_of_commute (h2 : (2 : K) ≠ 0) {h : GL (ι₁ ⊕ ι₂) K}
    (hc : h * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h) :
    (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K).toBlocks₁₂ = 0 ∧
      (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K).toBlocks₂₁ = 0 := by
  have e := congrArg (fun x : GL (ι₁ ⊕ ι₂) K => (x : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K)) hc
  simp only [Units.val_mul, coe_blockR, Units.val_neg, Units.val_one] at e
  rw [← fromBlocks_toBlocks (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K), fromBlocks_multiply,
    fromBlocks_multiply] at e
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul] at e
  obtain ⟨-, hB, hC, -⟩ := fromBlocks_inj.mp e
  constructor
  · ext i j
    have h1 := congrFun (congrFun hB i) j
    simp only [Matrix.neg_apply, Matrix.zero_apply] at h1 ⊢
    have h3 : (2 : K) * (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K).toBlocks₁₂ i j = 0 := by
      linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  · ext i j
    have h1 := congrFun (congrFun hC i) j
    simp only [Matrix.neg_apply, Matrix.zero_apply] at h1 ⊢
    have h3 : (2 : K) * (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K).toBlocks₂₁ i j = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left h2

theorem inv_commute_blockR {h : GL (ι₁ ⊕ ι₂) K}
    (hc : h * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h) :
    h⁻¹ * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h⁻¹ := by
  calc h⁻¹ * blockR ι₁ (-1 : GL ι₂ K) = h⁻¹ * (blockR ι₁ (-1 : GL ι₂ K) * h) * h⁻¹ := by group
    _ = h⁻¹ * (h * blockR ι₁ (-1 : GL ι₂ K)) * h⁻¹ := by rw [hc]
    _ = blockR ι₁ (-1 : GL ι₂ K) * h⁻¹ := by group

theorem eq_fromBlocks_of_commute (h2 : (2 : K) ≠ 0) {h : GL (ι₁ ⊕ ι₂) K}
    (hc : h * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h) :
    (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K) =
      fromBlocks (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K).toBlocks₁₁ 0 0
        (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K).toBlocks₂₂ := by
  obtain ⟨hB, hC⟩ := toBlocks_eq_zero_of_commute h2 hc
  conv_lhs => rw [← fromBlocks_toBlocks (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K), hB, hC]

@[expose] def restrL (h2 : (2 : K) ≠ 0) (h : GL (ι₁ ⊕ ι₂) K)
    (hc : h * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h) : GL ι₁ K :=
  ⟨(h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K).toBlocks₁₁,
    ((h⁻¹ : GL (ι₁ ⊕ ι₂) K) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K).toBlocks₁₁, by
      have e := congrArg Matrix.toBlocks₁₁ (Units.mul_inv h)
      rw [eq_fromBlocks_of_commute h2 hc, eq_fromBlocks_of_commute h2 (inv_commute_blockR hc),
        fromBlocks_multiply, toBlocks_fromBlocks₁₁] at e
      simpa [← fromBlocks_one] using e, by
      have e := congrArg Matrix.toBlocks₁₁ (Units.inv_mul h)
      rw [eq_fromBlocks_of_commute h2 hc, eq_fromBlocks_of_commute h2 (inv_commute_blockR hc),
        fromBlocks_multiply, toBlocks_fromBlocks₁₁] at e
      simpa [← fromBlocks_one] using e⟩

theorem coe_restrL (h2 : (2 : K) ≠ 0) (h : GL (ι₁ ⊕ ι₂) K)
    (hc : h * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h) :
    ((restrL h2 h hc : GL ι₁ K) : Matrix ι₁ ι₁ K) =
      (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K).toBlocks₁₁ :=
  rfl

theorem coe_restrL_inv (h2 : (2 : K) ≠ 0) (h : GL (ι₁ ⊕ ι₂) K)
    (hc : h * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h) :
    (((restrL h2 h hc)⁻¹ : GL ι₁ K) : Matrix ι₁ ι₁ K) =
      ((h⁻¹ : GL (ι₁ ⊕ ι₂) K) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K).toBlocks₁₁ :=
  rfl

theorem conj_blockL (h2 : (2 : K) ≠ 0) {h : GL (ι₁ ⊕ ι₂) K}
    (hc : h * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h) (g : GL ι₁ K) :
    h * blockL ι₂ g * h⁻¹ = blockL ι₂ (restrL h2 h hc * g * (restrL h2 h hc)⁻¹) := by
  have hmul : (h : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K) *
      ((h⁻¹ : GL (ι₁ ⊕ ι₂) K) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K) = 1 := Units.mul_inv h
  rw [eq_fromBlocks_of_commute h2 hc, eq_fromBlocks_of_commute h2 (inv_commute_blockR hc),
    fromBlocks_multiply] at hmul
  have h22 := congrArg Matrix.toBlocks₂₂ hmul
  simp only [toBlocks_fromBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero, zero_add] at h22
  rw [← fromBlocks_one, toBlocks_fromBlocks₂₂] at h22
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, eq_fromBlocks_of_commute h2 hc, coe_blockL,
    eq_fromBlocks_of_commute h2 (inv_commute_blockR hc), fromBlocks_multiply,
    fromBlocks_multiply, coe_blockL, Units.val_mul, Units.val_mul, coe_restrL, coe_restrL_inv]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  rw [h22]

theorem restrL_mem_isoGroup (h2 : (2 : K) ≠ 0) {h : GL (ι₁ ⊕ ι₂) K}
    (hc : h * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h)
    (hh : h ∈ isoGroup (sumQ Q₁ Q₂)) : restrL h2 h hc ∈ isoGroup Q₁ := by
  intro x
  have e := hh (Sum.elim x 0)
  rw [eq_fromBlocks_of_commute h2 hc, fromBlocks_mulVec] at e
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, add_zero, zero_mulVec] at e
  rw [sumQ_elim, sumQ_elim] at e
  rw [coe_restrL]
  exact add_right_cancel e

@[expose] def blockSub (Q₁ : (ι₁ → K) → K) (ι₂ : Type) [Fintype ι₂] [DecidableEq ι₂] :
    Subgroup (GL (ι₁ ⊕ ι₂) K) :=
  (StatedOmega Q₁).map (blockL ι₂)

theorem blockSub_le_statedOmega : blockSub Q₁ ι₂ ≤ StatedOmega (sumQ Q₁ Q₂) :=
  map_blockL_statedOmega_le

theorem blockSub_le_centralizer :
    blockSub Q₁ ι₂ ≤ centralizer {blockR ι₁ (-1 : GL ι₂ K)} := by
  rintro _ ⟨g, -, rfl⟩
  rw [mem_centralizer_singleton_iff]
  exact commute_blockL_blockR g (-1 : GL ι₂ K)

theorem conj_mem_blockSub (h2 : (2 : K) ≠ 0) {h : GL (ι₁ ⊕ ι₂) K}
    (hc : h * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h)
    (hh : h ∈ isoGroup (sumQ Q₁ Q₂)) {x : GL (ι₁ ⊕ ι₂) K} (hx : x ∈ blockSub Q₁ ι₂) :
    h * x * h⁻¹ ∈ blockSub Q₁ ι₂ := by
  obtain ⟨g, hg, rfl⟩ := hx
  refine ⟨restrL h2 h hc * g * (restrL h2 h hc)⁻¹,
    conj_mem_statedOmega (restrL_mem_isoGroup h2 hc hh) hg, ?_⟩
  exact (conj_blockL h2 hc g).symm

@[expose] def blockSubEquiv : blockSub Q₁ ι₂ ≃* StatedOmega Q₁ :=
  ((StatedOmega Q₁).equivMapOfInjective (blockL ι₂) blockL_injective).symm

end Block

section RBlock

variable {ι₁ ι₂ σ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Fintype σ] [DecidableEq σ] (e : ι₁ ⊕ ι₂ ≃ σ) {Q₁ : (ι₁ → K) → K} {Q₂ : (ι₂ → K) → K}
  {Q : (σ → K) → K}

variable (Q₁) in
@[expose] def rblock : Subgroup (GL σ K) :=
  (blockSub Q₁ ι₂).map (reGL e).toMonoidHom

@[expose] def uMat : GL σ K :=
  reGL e (blockR ι₁ (-1 : GL ι₂ K))

theorem rblock_le_statedOmega (hQ : pullQ e Q = sumQ Q₁ Q₂) : rblock e Q₁ ≤ StatedOmega Q := by
  rw [← map_reGL_statedOmega e Q, hQ]
  exact map_mono blockSub_le_statedOmega

theorem rblock_le_centralizer : rblock e Q₁ ≤ centralizer {uMat e} := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h := mem_centralizer_singleton_iff.mp (blockSub_le_centralizer hx)
  change reGL e x * reGL e (blockR ι₁ (-1 : GL ι₂ K)) =
    reGL e (blockR ι₁ (-1 : GL ι₂ K)) * reGL e x
  rw [← map_mul, ← map_mul, h]

theorem conj_mem_rblock (h2 : (2 : K) ≠ 0) (hQ : pullQ e Q = sumQ Q₁ Q₂) {h : GL σ K}
    (hh : h ∈ isoGroup Q) (hc : h * uMat e = uMat e * h) {x : GL σ K} (hx : x ∈ rblock e Q₁) :
    h * x * h⁻¹ ∈ rblock e Q₁ := by
  obtain ⟨y, hy, rfl⟩ := hx
  set h' := (reGL e).symm h with hh'_def
  have hh' : h' ∈ isoGroup (sumQ Q₁ Q₂) := by
    rw [← hQ, ← reGL_mem_isoGroup_iff e, hh'_def, MulEquiv.apply_symm_apply]
    exact hh
  have hc' : h' * blockR ι₁ (-1 : GL ι₂ K) = blockR ι₁ (-1 : GL ι₂ K) * h' := by
    apply (reGL e).injective
    rw [map_mul, map_mul, hh'_def, MulEquiv.apply_symm_apply]
    exact hc
  refine ⟨h' * y * h'⁻¹, conj_mem_blockSub h2 hc' hh' hy, ?_⟩
  change reGL e (h' * y * h'⁻¹) = h * reGL e y * h⁻¹
  rw [map_mul, map_mul, map_inv, hh'_def, MulEquiv.apply_symm_apply]

@[expose] def rblockEquiv : rblock e Q₁ ≃* StatedOmega Q₁ :=
  ((blockSub Q₁ ι₂).equivMapOfInjective (reGL e).toMonoidHom (reGL e).injective).symm.trans
    blockSubEquiv

theorem uMat_not_mem_rblock (h2 : (2 : K) ≠ 0) [Nonempty ι₂] : uMat e ∉ rblock e Q₁ := by
  rintro ⟨x, ⟨g, -, rfl⟩, hx⟩
  have hx' : blockL ι₂ g = blockR ι₁ (-1 : GL ι₂ K) := (reGL e).injective hx
  have e1 := congrArg (fun y : GL (ι₁ ⊕ ι₂) K => (y : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K)) hx'
  simp only [coe_blockL, coe_blockR] at e1
  obtain ⟨-, -, -, h22⟩ := fromBlocks_inj.mp e1
  obtain ⟨j⟩ := ‹Nonempty ι₂›
  have h3 : (1 : K) = -1 := by
    simpa [Matrix.neg_apply, Matrix.one_apply_eq] using congrFun (congrFun h22 j) j
  exact h2 (by linear_combination h3)

theorem neg_one_mul_uMat_mem_rblock (h : (-1 : GL ι₁ K) ∈ StatedOmega Q₁) :
    (-1 : GL σ K) * uMat e ∈ rblock e Q₁ := by
  have hLR := blockL_neg_one_mul_blockR_neg_one (K := K) (ι₁ := ι₁) (ι₂ := ι₂)
  have hRR : blockR ι₁ (-1 : GL ι₂ K) * blockR ι₁ (-1 : GL ι₂ K) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  refine ⟨blockL ι₂ (-1 : GL ι₁ K), ⟨-1, h, rfl⟩, ?_⟩
  change reGL e (blockL ι₂ (-1 : GL ι₁ K)) = -1 * reGL e (blockR ι₁ (-1 : GL ι₂ K))
  rw [← reGL_neg_one e, ← map_mul, ← hLR, mul_assoc, hRR, mul_one]

end RBlock

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
