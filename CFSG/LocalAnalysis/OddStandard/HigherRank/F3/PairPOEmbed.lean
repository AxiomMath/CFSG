module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPOGeneric
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBRBlock

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup Matrix CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit.T1.P54

section Coords

variable {K : Type} [Field K] {ι₁ ι₂ σ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
  [DecidableEq ι₂] [Fintype σ] [DecidableEq σ] (e : ι₁ ⊕ ι₂ ≃ σ)

theorem uMat_mulVec_inl' (x : σ → K) (i : ι₁) :
    (((DB.uMat e : GL σ K) : Matrix σ σ K) *ᵥ x) (e (.inl i)) = x (e (.inl i)) := by
  rw [DB.uMat, DB.reGL_mulVec, Function.comp_apply, Equiv.symm_apply_apply, DB.blockR_mulVec]
  rfl

theorem uMat_mulVec_inr' (x : σ → K) (j : ι₂) :
    (((DB.uMat e : GL σ K) : Matrix σ σ K) *ᵥ x) (e (.inr j)) = -x (e (.inr j)) := by
  rw [DB.uMat, DB.reGL_mulVec, Function.comp_apply, Equiv.symm_apply_apply, DB.blockR_mulVec]
  simp [Units.val_neg, neg_mulVec]

theorem neg_one_mul_uMat_mulVec_inl (x : σ → K) (i : ι₁) :
    ((((-1 : GL σ K) * DB.uMat e : GL σ K) : Matrix σ σ K) *ᵥ x) (e (.inl i)) =
      -x (e (.inl i)) := by
  rw [neg_one_mul, Units.val_neg, Matrix.neg_mulVec, Pi.neg_apply, uMat_mulVec_inl']

theorem neg_one_mul_uMat_mulVec_inr (x : σ → K) (j : ι₂) :
    ((((-1 : GL σ K) * DB.uMat e : GL σ K) : Matrix σ σ K) *ᵥ x) (e (.inr j)) =
      x (e (.inr j)) := by
  rw [neg_one_mul, Units.val_neg, Matrix.neg_mulVec, Pi.neg_apply, uMat_mulVec_inr', neg_neg]

theorem neg_one_mul_uMat_not_mem_scalars (h2 : (2 : K) ≠ 0) [Nonempty ι₁] [Nonempty ι₂] :
    (-1 : GL σ K) * DB.uMat e ∉ StatedScalars σ K := by
  rintro ⟨s, hs⟩
  obtain ⟨i⟩ := ‹Nonempty ι₁›
  obtain ⟨j⟩ := ‹Nonempty ι₂›
  have hsc : ∀ k : σ, ((((Matrix.GeneralLinearGroup.scalar σ) s : GL σ K) : Matrix σ σ K) *ᵥ
      (fun _ => (1 : K))) k = (s : K) := by
    intro k
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    simp
  have h1 := hsc (e (.inl i))
  have h2' := hsc (e (.inr j))
  rw [hs, neg_one_mul_uMat_mulVec_inl] at h1
  rw [hs, neg_one_mul_uMat_mulVec_inr] at h2'
  apply h2
  linear_combination h2' - h1

end Coords

section Main

variable {K : Type} [Field K] [Finite K] {ι₁ ι₂ σ : Type} [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype σ] [DecidableEq σ]

theorem hasPOmegaMember_statedProj_of_split [Nonempty ι₁] [Nonempty ι₂] (h2 : (2 : K) ≠ 0)
    (e : ι₁ ⊕ ι₂ ≃ σ) {Q₁ : (ι₁ → K) → K} {Q₂ : (ι₂ → K) → K} {Q : (σ → K) → K}
    (hQ : DB.pullQ e Q = DB.sumQ Q₁ Q₂) (hneg : (-1 : GL ι₁ K) ∈ StatedOmega Q₁)
    (hX : POmegaBlock ↥(StatedOmega Q₁)) [IsSimpleGroup (StatedProj (StatedOmega Q))] :
    HasPOmegaMember (StatedProj (StatedOmega Q)) := by
  have hcR : (-1 : GL σ K) * DB.uMat e ∈ DB.rblock e Q₁ :=
    DB.neg_one_mul_uMat_mem_rblock e hneg
  have hRle : DB.rblock e Q₁ ≤ StatedOmega Q := DB.rblock_le_statedOmega e hQ
  have hcomm : ∀ g : GL σ K, g * ((-1 : GL σ K) * (DB.uMat e : GL σ K)) =
      ((-1 : GL σ K) * (DB.uMat e : GL σ K)) * g ↔
      g * (DB.uMat e : GL σ K) = (DB.uMat e : GL σ K) * g := by
    intro g
    rw [neg_one_mul, mul_neg, neg_mul, neg_inj]
  have hu : (DB.uMat e : GL σ K) * (DB.uMat e : GL σ K) = 1 := by
    rw [DB.uMat, ← map_mul, ← map_mul, neg_one_mul, neg_neg, map_one, map_one]
  have hle : (DB.rblock e Q₁).subgroupOf (StatedOmega Q) ≤
      centralizer ({(⟨(-1 : GL σ K) * DB.uMat e, hRle hcR⟩ : ↥(StatedOmega Q))} :
        Set ↥(StatedOmega Q)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hx' : (x : GL σ K) ∈ DB.rblock e Q₁ := Subgroup.mem_subgroupOf.mp hx
    exact (hcomm x).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (DB.rblock_le_centralizer e hx'))
  refine hasPOmegaMember_of_cover_block
    (QuotientGroup.mk' ((StatedScalars σ K).subgroupOf (StatedOmega Q)))
    (QuotientGroup.mk'_surjective _) ?_ ((DB.rblock e Q₁).subgroupOf (StatedOmega Q))
    ⟨(-1 : GL σ K) * DB.uMat e, hRle hcR⟩ (Subgroup.mem_subgroupOf.mpr hcR) ?_ ?_ hle ?_ ?_
  · rw [QuotientGroup.ker_mk']
    exact LieType.Universal.Spin.statedScalars_subgroupOf_le_center _
  · apply Subtype.ext
    show ((-1 : GL σ K) * DB.uMat e) * ((-1 : GL σ K) * DB.uMat e) = 1
    rw [neg_one_mul, neg_mul_neg, hu]
  · intro h1
    exact neg_one_mul_uMat_not_mem_scalars e h2
      (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
  · refine (Subgroup.normal_subgroupOf_iff hle).2 fun j a hj ha => ?_
    have hj' : (j : GL σ K) ∈ DB.rblock e Q₁ := Subgroup.mem_subgroupOf.mp hj
    have ha' : (a : GL σ K) * ((-1 : GL σ K) * (DB.uMat e : GL σ K)) =
        ((-1 : GL σ K) * (DB.uMat e : GL σ K)) * a :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp ha)
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa using DB.conj_mem_rblock e h2 hQ (DB.statedOmega_le_isoGroup Q a.2)
        ((hcomm a).mp ha') hj')
  · exact POmegaBlock.of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hRle).trans (DB.rblockEquiv e)).symm hX

end Main

end CFSG.OddStandard.HigherRank.F3
