module


public import CFSG.LinearAlgebra.CoprimeActions.DistinctCharacterEigenvectorIndependent

public section

namespace CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

@[expose] def weightSpace {F V E : Type*} [Field F] [AddCommGroup V] [Module F V] [Group E]
    (τ : Representation F E V) (χ : E →* Fˣ) : Submodule F V where
  carrier := {v | ∀ g, τ g v = (χ g : F) • v}
  add_mem' := by
    intro a b ha hb g
    simp [map_add, ha g, hb g, smul_add]
  zero_mem' := by intro g; simp
  smul_mem' := by
    intro c a ha g
    simp [map_smul, ha g, smul_comm c]

theorem mem_weightSpace {F V E : Type*} [Field F] [AddCommGroup V] [Module F V] [Group E]
    (τ : Representation F E V) (χ : E →* Fˣ) (v : V) :
    v ∈ weightSpace τ χ ↔ ∀ g, τ g v = (χ g : F) • v := Iff.rfl

theorem independent {F V E I : Type*} [Field F] [AddCommGroup V] [Module F V] [Group E]
    (τ : Representation F E V) (χ : I → (E →* Fˣ)) (hχ : Function.Injective χ) :
    iSupIndep (fun i => weightSpace τ (χ i)) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  by_contra hne
  set s' : Finset I := s.filter (fun j => v j ≠ 0) with hs'
  have hli : LinearIndependent F (fun j : s' => v j) := by
    refine DistinctCharacterEigenvectorIndependent.linearIndependent τ (fun j : s' => χ j)
      (fun j => v j) (fun j => (Finset.mem_filter.1 j.2).2) (fun j g => hv j
        (Finset.mem_filter.1 j.2).1 g) ?_
    intro a b hab
    exact Subtype.ext (hχ hab)
  have h0 : ∑ j : s', (1 : F) • v j = 0 := by
    simp only [one_smul]
    rw [Finset.sum_coe_sort s' (fun j => v j), hs', Finset.sum_filter_of_ne (fun j _ h => h)]
    exact hsum
  have := Fintype.linearIndependent_iff.1 hli (fun _ => 1) h0 ⟨i, Finset.mem_filter.2 ⟨hi, hne⟩⟩
  exact one_ne_zero this

theorem ext_on_weights {F V W E I : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [Group E]
    (τ : Representation F E V) (χ : I → (E →* Fˣ))
    (htop : ⨆ i, weightSpace τ (χ i) = ⊤) (f g : V →ₗ[F] W)
    (h : ∀ i, ∀ v ∈ weightSpace τ (χ i), f v = g v) : f = g := by
  have hle : (⊤ : Submodule F V) ≤ LinearMap.eqLocus f g := by
    rw [← htop]
    exact iSup_le fun i v hv => h i v hv
  ext v
  exact hle (Submodule.mem_top (x := v))

end CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence
