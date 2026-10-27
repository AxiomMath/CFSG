module

public import CFSG.LieType.Chevalley.GraphFixedParabolicCells

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem exists_reduced_orbitWord
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    ∃ ω : List (Fin t.foldedTag.rank), (ω.map t.orbitReflection).prod = w ∧
      ω.length = t.orbitLength w := by
  obtain ⟨ω, hω, hprod⟩ := (coxeterSystem t.foldedTag).exists_isReduced (foldedWeylEquiv t ⟨w, hw⟩)
  refine ⟨ω, ?_, ?_⟩
  · have h := foldedWeylEquiv_list_prod t ω
    rw [← hprod] at h
    exact congrArg Subtype.val ((foldedWeylEquiv t).injective h)
  · rw [orbitLength_eq t ⟨w, hw⟩, hprod, hω.eq]

theorem list_prod_orbitReflection_mem_foldedParabolicWeylGroup
    {J : Set (Fin t.foldedTag.rank)}
    {ω : List (Fin t.foldedTag.rank)} (hω : ∀ a ∈ ω, a ∈ J) :
    (ω.map t.orbitReflection).prod ∈ foldedParabolicWeylGroup t J :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨a, hω a ha, rfl⟩

variable (hσ : Function.Surjective σ)
include hσ

theorem eq_graphFixedParabolic_of_le
    {A : Subgroup (ModGL t.tag K)}
    (hB : graphFixedRootBorel t K σ ≤ A) (hA : A ≤ graphFixedRootGroup t K σ) :
    A = graphFixedParabolic t K σ
      {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ A} := by
  refine le_antisymm (fun g hg => ?_) (sup_le hB ((Subgroup.closure_le _).2 ?_))
  · have hg' : g ∈ (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := hA hg
    rw [graphFixedRootGroup_eq_iUnion hσ] at hg'
    obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hgw
    have hn : canonicalRep (coxeterSystem t.tag) K w ∈ A := by
      have e : canonicalRep (coxeterSystem t.tag) K w =
          b⁻¹ * (b * canonicalRep (coxeterSystem t.tag) K w * b') * b'⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hB hb)) hg) (inv_mem (hB hb'))
    obtain ⟨ω, hω, hlen⟩ := exists_reduced_orbitWord hw
    have hletters := fixed_reduced_word_Borel_extraction t K σ A hA hB w hw
      (fun b hb => mul_mem (mul_mem hn (hB hb)) (inv_mem hn)) ω hω hlen
    have hwJ : w ∈ foldedParabolicWeylGroup t
        {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ A} :=
      hω ▸ list_prod_orbitReflection_mem_foldedParabolicWeylGroup hletters
    exact graphFixedParabolicCells_subset _ ⟨w, hwJ, hgw⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ha

omit hσ

theorem fixed_Borel_overgroup_classification
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    ∀ A : Subgroup (ModGL t.tag K), graphFixedRootBorel t K σ.toRingHom ≤ A →
      A ≤ graphFixedRootGroup t K σ.toRingHom →
        A = graphFixedParabolic t K σ.toRingHom
            {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ A} ∧
          ∃! J : Set (Fin t.foldedTag.rank), A = graphFixedParabolic t K σ.toRingHom J := by
  intro A hB hA
  have hAJ := eq_graphFixedParabolic_of_le σ.surjective hB hA
  refine ⟨hAJ, ⟨_, hAJ, fun J hJ => ?_⟩⟩
  ext a
  rw [← canonicalRep_orbitReflection_mem_graphFixedParabolic_iff (K := K) (σ := σ.toRingHom)
    σ.surjective, ← hJ]
  rfl

end CFSG.LieType.Chevalley
