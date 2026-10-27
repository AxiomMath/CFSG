module

public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.Defs
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.Dictionary
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.Reduction
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.ReductionFixed
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.ReductionModel

public section

namespace CFSG.AGLEmbedding.TrialityTwo

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Pointwise

variable {T : Type} [Group T] {K : Type} [Field K] [Finite K]

theorem false_of_orderOf_eq_five (h5 : FiveFixedDichotomy)
    (h : StatedClassicalModel T .POmegaPlus 4 2 1) (hK : Nat.card K = 2 ^ 1)
    (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (α : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
    (hα : α ∉ inner (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) (h3 : α ^ 3 = 1)
    (x : StatedProj (StatedOmega (StatedQuadPlus 4 K))) (hx : α x = x) (hx5 : orderOf x = 5) :
    False := by
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨g, rfl⟩ := (omegaProjEquiv hK2).surjective x
  rw [MulEquiv.orderOf_eq] at hx5
  rw [omegaProjEquiv_apply] at hx
  have hdich := h5 K hK2 g hx5
  rw [← exists_mem_statedPointFamily_iff, ← exists_mem_solidFamilies_iff,
    exists_mem_solidFamilies_iff_of_apply_eq h hK e α hα h3 hx] at hdich
  exact iff_not_self hdich

theorem false_of_orderOf_eq_seven (h7 : SevenFixedRigid)
    (h : StatedClassicalModel T .POmegaPlus 4 2 1) (hK : Nat.card K = 2 ^ 1)
    (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (α : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
    (hα : α ∉ inner (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) (h3 : α ^ 3 = 1)
    (hfree : ∀ L : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K))), ⁅L, L⁆ = L →
      (∀ y ∈ L, α y = y) → L = ⊥)
    (x : StatedProj (StatedOmega (StatedQuadPlus 4 K))) (hx : α x = x) (hx7 : orderOf x = 7) :
    False := by
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨g, rfl⟩ := (omegaProjEquiv hK2).surjective x
  rw [MulEquiv.orderOf_eq] at hx7
  rw [omegaProjEquiv_apply] at hx
  obtain ⟨hne, hperf, hrigid⟩ := h7 K hK2 g hx7
  set F₀ := statedPointFamily (coe_quadPlus 4 K)
  set 𝓕 : Set (Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) :=
    {Y | Y ∈ F₀ ∨ Y ∈ α • F₀ ∨ Y ∈ (α ^ 2) • F₀}
  have h𝓕 : ∀ Y, Y ∈ 𝓕 ↔ ∃ W, (IsSingularPoint W ∨ W ∈ singularSubspaces (quadPlus 4 K) 4) ∧
      Y = statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W := by
    intro Y
    change (Y ∈ F₀ ∨ Y ∈ α • F₀ ∨ Y ∈ (α ^ 2) • F₀) ↔ _
    rw [← mem_solidFamilies_iff_mem_smul h hK e α hα h3, mem_statedPointFamily_iff,
      mem_solidFamilies_iff]
    constructor
    · rintro (⟨W, hW, rfl⟩ | ⟨W, hW, rfl⟩)
      · exact ⟨W, Or.inl hW, rfl⟩
      · exact ⟨W, Or.inr hW, rfl⟩
    · rintro ⟨W, hW | hW, rfl⟩
      · exact Or.inl ⟨W, hW, rfl⟩
      · exact Or.inr ⟨W, hW, rfl⟩
  have hS : ∀ Y ∈ {Y | Y ∈ 𝓕 ∧ QuotientGroup.mk' _ g ∈ Y}, α • Y ∈
      {Y | Y ∈ 𝓕 ∧ QuotientGroup.mk' _ g ∈ Y} := by
    rintro Y ⟨hY, hgY⟩
    refine ⟨?_, (mem_smul_subgroup_iff_of_apply_eq hx Y).2 hgY⟩
    rcases hY with hY | hY | hY
    · exact Or.inr (Or.inl (Set.smul_mem_smul_set hY))
    · refine Or.inr (Or.inr ?_)
      rw [pow_two, mul_smul]
      exact Set.smul_mem_smul_set hY
    · refine Or.inl ?_
      have hY' := Set.smul_mem_smul_set (a := α) hY
      rwa [← mul_smul, ← pow_succ', h3, one_smul] at hY'
  have hL := map_iInf_eq_of_smul_mem h3 hS
  have hHL := map_fixedObjectsStabilizer_eq_iInf hK2 g 𝓕 h𝓕
  set L := ⨅ Y ∈ {Y | Y ∈ 𝓕 ∧ QuotientGroup.mk' _ g ∈ Y}, Y
  set ψ : fixedObjectsStabilizer g ≃* L :=
    ((omegaProjEquiv hK2).subgroupMap (fixedObjectsStabilizer g)).trans
      (MulEquiv.subgroupCongr hHL)
  set β : MulAut (fixedObjectsStabilizer g) := MulAut.congr ψ.symm (restrictAut α L hL)
  have hβ : ∀ y, β y = ψ.symm (restrictAut α L hL (ψ y)) := fun _ => rfl
  have hβg : β ⟨g, self_mem_fixedObjectsStabilizer g⟩ = ⟨g, self_mem_fixedObjectsStabilizer g⟩ := by
    rw [hβ, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [restrictAut_apply]
    exact hx
  have hβ3 : β ^ 3 = 1 := by
    rw [← map_pow, restrictAut_pow_three α h3 L hL, map_one]
  have hβ1 := hrigid β hβg hβ3
  have hfix : ∀ y ∈ L, α y = y := by
    intro y hy
    have h1 : β (ψ.symm ⟨y, hy⟩) = ψ.symm ⟨y, hy⟩ := by rw [hβ1, MulAut.one_apply]
    rw [hβ, MulEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq] at h1
    have h2 := congrArg Subtype.val h1
    rwa [restrictAut_apply] at h2
  have hLperf : ⁅L, L⁆ = L := by rw [← hHL, ← Subgroup.map_commutator, hperf]
  apply hne
  exact (Subgroup.map_eq_bot_iff_of_injective _ (omegaProjEquiv hK2).injective).mp
    (hHL.trans (hfree L hLperf hfix))

theorem kFactThreeCentTrialityTwo_of (h5 : FiveFixedDichotomy) (h7 : SevenFixedRigid) :
    CFSG.AGLEmbedding.KFactThreeCentTrialityTwo :=
  kFactThreeCentTrialityTwo_of_model fun _ _ h _ _ _ hK e α hα h3 hfree x hx hx57 =>
    hx57.elim (false_of_orderOf_eq_five h5 h hK e α hα h3 x hx)
      (false_of_orderOf_eq_seven h7 h hK e α hα h3 hfree x hx)

end CFSG.AGLEmbedding.TrialityTwo
