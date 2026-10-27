module

public import CFSG.LieType.Chevalley.OrthogonalUnionBruhat
import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedCells

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem unionRoots_univ_eq_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    unionRoots χ (Set.univ : Set (KernelComponent χ)) = kernelRoots χ :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, Set.mem_univ _⟩⟩


theorem exists_kernelRoots_bruhat_factor {τ : Tag} {K : Type} [Field K] {M : Type*}
    [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {s : ModGL τ K}
    (hs : s ∈ rootSpan τ K (kernelRoots χ)) :
    ∃ w ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots χ),
      ∃ h ∈ torusGroup τ K, ∃ u ∈ rootSpan τ K (posRoots (kernelRoots χ)),
        ∃ v ∈ rootSpan τ K {α | α ∈ posRoots (kernelRoots χ) ∧ height (w • α) < 0},
          s = h * u * canonicalRep (coxeterSystem τ) K w * v := by
  have hn : ∀ β ∈ unionSimpleRoots χ (Set.univ : Set (KernelComponent χ)),
      rootWeylOne τ K β ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ∧
        rootWeylOne τ K β ∈ monomialSubgroup τ K ∧
        MapsRootLines (rootWeylOne τ K β) (rootReflection β) :=
    fun _ hβ => rootWeylOne_spec (isRoot_of_mem_unionSimpleRoots hβ)
  obtain ⟨hlift, hdc, hcover, -, hbij, hborel, -, -, -, -⟩ :=
    orthogonal_union_Bruhat_cell_factorization τ K χ Set.univ (rootWeylOne τ K) hn
  have hs' : s ∈ ⋃ w ∈ unionWeylGroup χ (Set.univ : Set (KernelComponent χ)),
      unionCell K χ Set.univ (rootWeylOne τ K) w := by
    rw [← hcover]
    show s ∈ rootSpan τ K (unionRoots χ Set.univ)
    rw [unionRoots_univ_eq_kernelRoots]
    exact hs
  obtain ⟨w, hw, hsw⟩ := Set.mem_iUnion₂.1 hs'
  obtain ⟨g, hg⟩ := hlift w hw
  rw [← hdc w hw g hg] at hsw
  obtain ⟨⟨b, v⟩, ⟨hb, hv⟩, hbv⟩ := (hbij w hw g hg).surjOn hsw
  dsimp only at hb hv hbv
  rw [hborel] at hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb
  obtain ⟨w', k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets
    (unionMonomial_le_monomialSubgroup hn hg.1)
  have hww : w' = w := by
    have hmaps : MapsRootLines (k * canonicalRep (coxeterSystem τ) K w') w' := by
      simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w')
    have hg2 : MapsRootLines (k * canonicalRep (coxeterSystem τ) K w') w := by
      rw [← hgk]
      exact hg.2
    exact hmaps.unique hg2
  rw [hww] at hgk
  have hsimple : unionSimpleRoots χ (Set.univ : Set (KernelComponent χ)) ⊆ kernelRoots χ := by
    intro β hβ
    have h := mem_unionRoots_of_mem_unionSimpleRoots hβ
    rwa [unionRoots_univ_eq_kernelRoots] at h
  have hclos : w ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots χ) := by
    unfold unionWeylGroup at hw
    exact Subgroup.closure_mono (Set.image_mono hsimple) hw
  have hroots : ∀ α ∈ posRoots (kernelRoots χ), IsRoot τ α := fun _ hα => hα.1.1
  have hnorm := CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (K := K) hroots
  have hu' : u ∈ rootSpan τ K (posRoots (kernelRoots χ)) := by
    rw [← unionRoots_univ_eq_kernelRoots χ]
    exact hu
  have hu'' : k⁻¹ * u * k ∈ rootSpan τ K (posRoots (kernelRoots χ)) := by
    have h := (Subgroup.mem_normalizer_iff.1 (hnorm (inv_mem hk)) u).1 hu'
    rwa [inv_inv] at h
  have hv' : v ∈ rootSpan τ K {α | α ∈ posRoots (kernelRoots χ) ∧ height (w • α) < 0} := by
    have e : unionInversionRoots χ (Set.univ : Set (KernelComponent χ)) w =
        {α | α ∈ posRoots (kernelRoots χ) ∧ height (w • α) < 0} := by
      unfold unionInversionRoots
      rw [unionRoots_univ_eq_kernelRoots]
    rw [← e]
    exact hv
  refine ⟨w, hclos, t * k, mul_mem (unionTorus_le_torusGroup ht) hk, k⁻¹ * u * k, hu'', v, hv', ?_⟩
  rw [← hbv, hgk]
  group

end CFSG.LieType.AlgebraicGroups
