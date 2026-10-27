module

public import CFSG.LieType.Chevalley.SignKernelComponentBorel
public import CFSG.LieType.Chevalley.OddRootPairSL2

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem componentWeylElt_mem_rootSubgroup_sup
    {v : (Fin τ.rank → ℤ) → WeylGroup τ} {j : (Fin τ.rank → ℤ) → Fin τ.rank}
    {β : Fin τ.rank → ℤ} (hβv : v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β) :
    componentWeylElt K v j β ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) := by
  rw [← map_conj_canonicalRep_closure_xUnit_yUnit hβv]
  refine ⟨weylElt τ K (j β) 1, ?_, rfl⟩
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
    (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩))) (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))

theorem rootSpan_eq_iSup_simpleRoots
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    rootSpan τ K Ψ = ⨆ β ∈ simpleRoots Ψ, (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)) := by
  classical
  have hr : 0 < τ.rank := by cases τ <;> decide
  have hex : ∀ β : Fin τ.rank → ℤ, ∃ w : WeylGroup τ, ∃ i : Fin τ.rank,
      IsRoot τ β → w • (Pi.single i 1 : Fin τ.rank → ℤ) = β := by
    intro β
    by_cases hβ : IsRoot τ β
    · obtain ⟨w, i, h⟩ := isRoot_iff_exists_smul_single.1 hβ
      exact ⟨w, i, fun _ => h⟩
    · exact ⟨1, ⟨0, hr⟩, fun h => absurd h hβ⟩
  choose v j hvj using hex
  set H := ⨆ β ∈ simpleRoots Ψ, (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)) with hH
  have hsimple : ∀ β ∈ simpleRoots Ψ, β ∈ Ψ := fun β hβ => (mem_simpleRoots.1 hβ).2.1.1
  have hle : ∀ β ∈ simpleRoots Ψ, rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ≤ H :=
    fun β hβ => le_iSup₂_of_le β hβ le_rfl
  have hn : ∀ β ∈ simpleRoots Ψ, componentWeylElt K v j β ∈ H := fun β hβ =>
    hle β hβ (componentWeylElt_mem_rootSubgroup_sup (hvj β (hΨ.isRoot β (hsimple β hβ))))
  have hlift : ∀ w ∈ componentWeylGroup Ψ, ∃ g ∈ H, g ∈ monomialSubgroup τ K ∧
      MapsRootLines g w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β, hβ, rfl⟩ := hx
      exact ⟨_, hn β hβ, componentWeylElt_mem_monomialSubgroup K v j β,
        mapsRootLines_componentWeylElt (hvj β (hΨ.isRoot β (hsimple β hβ)))⟩
    | one => exact ⟨1, one_mem _, one_mem _, mapsRootLines_one⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg, hgM, h⟩ := hx
      obtain ⟨g', hg', hgM', h'⟩ := hy
      exact ⟨g * g', mul_mem hg hg', mul_mem hgM hgM', h.mul h'⟩
    | inv x _ hx =>
      obtain ⟨g, hg, hgM, h⟩ := hx
      exact ⟨g⁻¹, inv_mem hg, inv_mem hgM, h.inv⟩
  refine le_antisymm (iSup₂_le fun α hα => ?_) (iSup₂_le fun β hβ => sup_le
    (le_iSup₂_of_le β (hsimple β hβ) le_rfl)
    (le_iSup₂_of_le (-β) (hΨ.neg_mem β (hsimple β hβ)) le_rfl))
  obtain ⟨w, hw, β, hβ, rfl⟩ := exists_smul_simpleRoot hΨ hα
  obtain ⟨g, hgH, hgM, hgw⟩ := hlift w hw
  intro x hx
  have hx' : x ∈ rootSpan τ K {w • β} := by
    rw [rootSpan, iSup_singleton]
    exact hx
  have h := conj_mem_rootSpan_of_mapsRootLines (inv_mem hgM) hgw.inv (S := {w • β})
    (by rintro _ rfl; exact hΨ.isRoot _ hα) hx'
  rw [Set.image_singleton, inv_inv, inv_smul_smul, rootSpan, iSup_singleton] at h
  have hb : g⁻¹ * x * g ∈ H := hle β hβ (Subgroup.mem_sup_left h)
  have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hgH hb) (inv_mem hgH)

end CFSG.ComponentClassification.CatLeafProof
