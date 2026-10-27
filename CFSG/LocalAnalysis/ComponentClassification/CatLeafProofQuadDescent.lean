module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Split

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

section Closure

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem rootSL2_mem_adjointGroup
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (A : SL2 k) : rootSL2 τ k β A ∈ adjointGroup τ k := by
  have h : rootSL2 τ k β A ∈ (rootSL2 τ k β).range := ⟨A, rfl⟩
  rw [range_rootSL2_of_isRoot hβ] at h
  exact sup_le (rootSubgroup_le_adjointGroup β) (rootSubgroup_le_adjointGroup (-β)) h

theorem closure_rootSL2_eq_map_pairSpan
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot τ β) (n : ℕ) :
    Subgroup.closure {g : ModGL τ k | ∃ β ∈ S, ∃ c ∈ frobeniusFixedField k p n,
        g = rootSL2 τ k β (uSL c) ∨ g = rootSL2 τ k β (vSL c)} =
      (pairSpan τ (frobeniusFixedField k p n) S).map
        (baseChangeGL (frobeniusFixedField k p n).subtype) := by
  have hmem : ∀ β ∈ S, ∀ A, rootSL2 τ (frobeniusFixedField k p n) β A ∈
      pairSpan τ (frobeniusFixedField k p n) S := fun β hβ A => by
    refine Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem hβ ?_)
    rw [← range_rootSL2_of_isRoot (hS β hβ)]
    exact ⟨A, rfl⟩
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, c, hc, rfl | rfl⟩
    · refine ⟨_, hmem β hβ (uSL ⟨c, hc⟩), ?_⟩
      rw [baseChangeGL_rootSL2_of_field, LieType.Chevalley.map_uSL]
      rfl
    · refine ⟨_, hmem β hβ (vSL ⟨c, hc⟩), ?_⟩
      rw [baseChangeGL_rootSL2_of_field, LieType.Chevalley.map_vSL]
      rfl
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun β hβ => ?_
    rw [← range_rootSL2_of_isRoot (hS β hβ)]
    refine range_le_of_uSL_vSL _ (fun c => ?_) (fun c => ?_)
    · rw [Subgroup.mem_comap, baseChangeGL_rootSL2_of_field, LieType.Chevalley.map_uSL]
      exact Subgroup.subset_closure ⟨β, hβ, c, c.2, Or.inl rfl⟩
    · rw [Subgroup.mem_comap, baseChangeGL_rootSL2_of_field, LieType.Chevalley.map_vSL]
      exact Subgroup.subset_closure ⟨β, hβ, c, c.2, Or.inr rfl⟩

end Closure

section Quad

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

@[expose] def quadGens
    (D : OrthogonalSemilinearFixedRootDatum τ p k) : Set (adjointGroup τ k) :=
  {g | ∃ β ∈ D.simpleRootsJ, ∃ c ∈ frobeniusFixedField k p (D.e * 2),
    (g : ModGL τ k) = rootSL2 τ k β (uSL c) ∨ (g : ModGL τ k) = rootSL2 τ k β (vSL c)}

@[expose] def quadGroup
    (D : OrthogonalSemilinearFixedRootDatum τ p k) : Subgroup (adjointGroup τ k) :=
  Subgroup.closure (quadGens D)

theorem map_subtype_quadGroup
    (D : OrthogonalSemilinearFixedRootDatum τ p k) :
    (quadGroup D).map (adjointGroup τ k).subtype =
      (pairSpan τ (frobeniusFixedField k p (D.e * 2)) D.simpleRootsJ).map
        (baseChangeGL (frobeniusFixedField k p (D.e * 2)).subtype) := by
  have hroot : ∀ β ∈ D.simpleRootsJ, IsRoot τ β := fun β hβ =>
    (D.mem_kernelRoots_of_mem_simpleRootsJ hβ).1
  rw [← closure_rootSL2_eq_map_pairSpan hroot, quadGroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨β, hβ, c, hc, hx⟩, rfl⟩
    exact ⟨β, hβ, c, hc, hx⟩
  · rintro ⟨β, hβ, c, hc, hg | hg⟩
    · exact ⟨⟨g, hg ▸ rootSL2_mem_adjointGroup (hroot β hβ) _⟩, ⟨β, hβ, c, hc, Or.inl hg⟩, rfl⟩
    · exact ⟨⟨g, hg ▸ rootSL2_mem_adjointGroup (hroot β hβ) _⟩, ⟨β, hβ, c, hc, Or.inr hg⟩, rfl⟩

theorem pow_mem_frobeniusFixedField_two
    (D : OrthogonalSemilinearFixedRootDatum τ p k) {O : Set (Fin τ.rank → ℤ)}
    (hO : orbitCard O = 1 ∨ orbitCard O = 2) (c : D.orbitField O) (j : ℕ) :
    (c : k) ^ D.q ^ j ∈ frobeniusFixedField k p (D.e * 2) := by
  have hc : (c : k) ^ p ^ (D.e * 2) = c := by
    have h := c.2
    change (c : k) ∈ frobeniusFixedField k p (D.e * orbitCard O) at h
    rw [mem_frobeniusFixedField] at h
    rcases hO with h1 | h2
    · rw [h1, mul_one] at h
      rw [mul_two, pow_add, pow_mul, h, h]
    · rwa [h2] at h
  rw [mem_frobeniusFixedField, ← pow_mul, mul_comm, pow_mul, hc]

theorem orbitGroup_le_map_quadGroup
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2) :
    D.orbitGroup ≤ (quadGroup D).map (adjointGroup τ k).subtype := by
  have hroot : ∀ β ∈ D.simpleRootsJ, IsRoot τ β := fun β hβ =>
    (D.mem_kernelRoots_of_mem_simpleRootsJ hβ).1
  rw [map_subtype_quadGroup, ← closure_rootSL2_eq_map_pairSpan hroot]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨O, hO, c, rfl | rfl⟩
  · show ((List.range (orbitCard O)).map fun j => D.orbitFactor O j (uSL c)).prod ∈ _
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    rw [D.orbitFactor_uSL]
    exact Subgroup.subset_closure ⟨_, D.subset_simpleRootsJ_of_mem_orbits hO (D.orbitVec_mem hO j),
      _, pow_mem_frobeniusFixedField_two D (hcard O hO) c j, Or.inl rfl⟩
  · show ((List.range (orbitCard O)).map fun j => D.orbitFactor O j (vSL c)).prod ∈ _
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    rw [D.orbitFactor_vSL]
    exact Subgroup.subset_closure ⟨_, D.subset_simpleRootsJ_of_mem_orbits hO (D.orbitVec_mem hO j),
      _, pow_mem_frobeniusFixedField_two D (hcard O hO) c j, Or.inr rfl⟩

end Quad

end CFSG.ComponentClassification.CatLeafProof
