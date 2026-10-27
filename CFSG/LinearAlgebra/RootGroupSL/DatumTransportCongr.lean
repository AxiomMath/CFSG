module

public import CFSG.LinearAlgebra.RootGroupSL.DatumGroups
public import CFSG.LinearAlgebra.RootGroupSL.DatumEquiv

public section

namespace CFSG.LinearAlgebra.RootGroupSL


variable {k E V V' : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V']

private lemma congr_symm_apply_apply (L : V ≃ₗ[k] V') (g : SpecialLinearGroup k V') (v : V) :
    ((SpecialLinearGroup.congr_linearEquiv L).symm g) v = L.symm (g (L v)) := by
  rw [SpecialLinearGroup.congr_linearEquiv_symm]
  exact SpecialLinearGroup.congr_linearEquiv_apply_apply L.symm g v

private lemma mem_range_comp_iff (L : V ≃ₗ[k] V') (ι : E →ₗ[k] V) (w : V') :
    w ∈ LinearMap.range (L.toLinearMap ∘ₗ ι) ↔ L.symm w ∈ LinearMap.range ι := by
  rw [LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by simpa using congrArg L.symm ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by simpa using congrArg L ht⟩

private lemma congr_symm_mem_datumQ_iff (L : V ≃ₗ[k] V') (ι : E →ₗ[k] V) (π : V →ₗ[k] E)
    (g : SpecialLinearGroup k V') :
    (SpecialLinearGroup.congr_linearEquiv L).symm g ∈ datumQ ι π ↔
      g ∈ datumQ (L.toLinearMap ∘ₗ ι) (π ∘ₗ L.symm.toLinearMap) := by
  constructor
  · intro hg
    obtain ⟨h1, h2, h3⟩ := hg
    refine ⟨?_, ?_, ?_⟩
    · intro t
      have h := h1 t
      rw [congr_symm_apply_apply L g (ι t)] at h
      simpa using congrArg L h
    · intro v hv
      have hv' : π (L.symm v) = 0 := by simpa using hv
      have h := h2 (L.symm v) hv'
      rw [congr_symm_apply_apply L g (L.symm v)] at h
      rw [LinearEquiv.apply_symm_apply] at h
      have hmap : L.symm (g v - v) ∈ LinearMap.range ι := by
        rw [map_sub]
        exact h
      exact (mem_range_comp_iff L ι (g v - v)).mpr hmap
    · intro v
      have h := h3 (L.symm v)
      rw [congr_symm_apply_apply L g (L.symm v)] at h
      rw [LinearEquiv.apply_symm_apply] at h
      rw [← map_sub] at h
      rw [LinearMap.comp_apply]
      exact h
  · intro hg
    obtain ⟨h1, h2, h3⟩ := hg
    refine ⟨?_, ?_, ?_⟩
    · intro t
      rw [congr_symm_apply_apply, LinearEquiv.symm_apply_eq]
      exact h1 t
    · intro v hv
      have hv' : (π ∘ₗ L.symm.toLinearMap) (L v) = 0 := by simpa using hv
      have h := h2 (L v) hv'
      have h' : L.symm (g (L v) - L v) ∈ LinearMap.range ι :=
        (mem_range_comp_iff L ι (g (L v) - L v)).mp h
      rw [map_sub] at h'
      rw [LinearEquiv.symm_apply_apply] at h'
      rw [congr_symm_apply_apply]
      exact h'
    · intro v
      have h := h3 (L v)
      have hgoal : (SpecialLinearGroup.congr_linearEquiv L).symm g v - v
          = L.symm (g (L v) - L v) := by
        rw [congr_symm_apply_apply]
        simp only [map_sub, LinearEquiv.symm_apply_apply]
      rw [hgoal]
      exact h

private lemma congr_symm_mem_datumQ0_iff (L : V ≃ₗ[k] V') (ι : E →ₗ[k] V) (π : V →ₗ[k] E)
    (g : SpecialLinearGroup k V') :
    (SpecialLinearGroup.congr_linearEquiv L).symm g ∈ datumQ0 ι π ↔
      g ∈ datumQ0 (L.toLinearMap ∘ₗ ι) (π ∘ₗ L.symm.toLinearMap) := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · intro v
      have h := h1 (L.symm v)
      rw [congr_symm_apply_apply L g (L.symm v)] at h
      rw [LinearEquiv.apply_symm_apply] at h
      have hmap : L.symm (g v - v) ∈ LinearMap.range ι := by
        rw [map_sub]
        exact h
      exact (mem_range_comp_iff L ι (g v - v)).mpr hmap
    · intro v hv
      have hv' : π (L.symm v) = 0 := by simpa using hv
      have h := h2 (L.symm v) hv'
      rw [congr_symm_apply_apply L g (L.symm v)] at h
      rw [LinearEquiv.apply_symm_apply] at h
      simpa using congrArg L h
  · intro hg
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · intro v
      have h := h1 (L v)
      have h' : L.symm (g (L v) - L v) ∈ LinearMap.range ι :=
        (mem_range_comp_iff L ι (g (L v) - L v)).mp h
      rw [map_sub] at h'
      rw [LinearEquiv.symm_apply_apply] at h'
      rw [congr_symm_apply_apply]
      exact h'
    · intro v hv
      have hv' : (π ∘ₗ L.symm.toLinearMap) (L v) = 0 := by simpa using hv
      have h := h2 (L v) hv'
      rw [congr_symm_apply_apply, h, LinearEquiv.symm_apply_apply]

private lemma congr_symm_mem_datumU1_iff (L : V ≃ₗ[k] V') (ι : E →ₗ[k] V)
    (g : SpecialLinearGroup k V') :
    (SpecialLinearGroup.congr_linearEquiv L).symm g ∈ datumU1 ι ↔
      g ∈ datumU1 (L.toLinearMap ∘ₗ ι) := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · intro v
      have h := h1 (L.symm v)
      rw [congr_symm_apply_apply L g (L.symm v)] at h
      rw [LinearEquiv.apply_symm_apply] at h
      have hmap : L.symm (g v - v) ∈ LinearMap.range ι := by
        rw [map_sub]
        exact h
      exact (mem_range_comp_iff L ι (g v - v)).mpr hmap
    · intro t
      have h := h2 t
      rw [congr_symm_apply_apply L g (ι t)] at h
      simpa using congrArg L h
  · intro hg
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · intro v
      have h := h1 (L v)
      have h' : L.symm (g (L v) - L v) ∈ LinearMap.range ι :=
        (mem_range_comp_iff L ι (g (L v) - L v)).mp h
      rw [map_sub] at h'
      rw [LinearEquiv.symm_apply_apply] at h'
      rw [congr_symm_apply_apply]
      exact h'
    · intro t
      rw [congr_symm_apply_apply, LinearEquiv.symm_apply_eq]
      exact h2 t

private lemma congr_symm_mem_datumU2_iff (L : V ≃ₗ[k] V') (π : V →ₗ[k] E)
    (g : SpecialLinearGroup k V') :
    (SpecialLinearGroup.congr_linearEquiv L).symm g ∈ datumU2 π ↔
      g ∈ datumU2 (π ∘ₗ L.symm.toLinearMap) := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · intro v
      have h := h1 (L.symm v)
      rw [congr_symm_apply_apply L g (L.symm v)] at h
      rw [LinearEquiv.apply_symm_apply] at h
      rw [← map_sub] at h
      rw [LinearMap.comp_apply]
      exact h
    · intro v hv
      have hv' : π (L.symm v) = 0 := by simpa using hv
      have h := h2 (L.symm v) hv'
      rw [congr_symm_apply_apply L g (L.symm v)] at h
      rw [LinearEquiv.apply_symm_apply] at h
      simpa using congrArg L h
  · intro hg
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · intro v
      have h := h1 (L v)
      have hgoal : (SpecialLinearGroup.congr_linearEquiv L).symm g v - v
          = L.symm (g (L v) - L v) := by
        rw [congr_symm_apply_apply]
        simp only [map_sub, LinearEquiv.symm_apply_apply]
      rw [hgoal]
      exact h
    · intro v hv
      have hv' : (π ∘ₗ L.symm.toLinearMap) (L v) = 0 := by simpa using hv
      have h := h2 (L v) hv'
      rw [congr_symm_apply_apply, h, LinearEquiv.symm_apply_apply]

theorem map_datumQ_congr (L : V ≃ₗ[k] V') (ι : E →ₗ[k] V) (π : V →ₗ[k] E) :
    (datumQ ι π).map (SpecialLinearGroup.congr_linearEquiv L).toMonoidHom =
      datumQ (L.toLinearMap ∘ₗ ι) (π ∘ₗ L.symm.toLinearMap) := by
  ext g
  rw [Subgroup.mem_map_equiv]
  exact congr_symm_mem_datumQ_iff L ι π g

theorem map_datumQ0_congr (L : V ≃ₗ[k] V') (ι : E →ₗ[k] V) (π : V →ₗ[k] E) :
    (datumQ0 ι π).map (SpecialLinearGroup.congr_linearEquiv L).toMonoidHom =
      datumQ0 (L.toLinearMap ∘ₗ ι) (π ∘ₗ L.symm.toLinearMap) := by
  ext g
  rw [Subgroup.mem_map_equiv]
  exact congr_symm_mem_datumQ0_iff L ι π g

theorem map_datumU1_congr (L : V ≃ₗ[k] V') (ι : E →ₗ[k] V) :
    (datumU1 ι).map (SpecialLinearGroup.congr_linearEquiv L).toMonoidHom =
      datumU1 (L.toLinearMap ∘ₗ ι) := by
  ext g
  rw [Subgroup.mem_map_equiv]
  exact congr_symm_mem_datumU1_iff L ι g

theorem map_datumU2_congr (L : V ≃ₗ[k] V') (π : V →ₗ[k] E) :
    (datumU2 π).map (SpecialLinearGroup.congr_linearEquiv L).toMonoidHom =
      datumU2 (π ∘ₗ L.symm.toLinearMap) := by
  ext g
  rw [Subgroup.mem_map_equiv]
  exact congr_symm_mem_datumU2_iff L π g

variable [Module.Finite k V] [Module.Finite k V'] [Module.Finite k E]

private lemma congr_datumElt (L : V ≃ₗ[k] V') (ι : E →ₗ[k] V) (π : V →ₗ[k] E)
    (h : ∀ t, π (ι t) = 0) (h' : ∀ t, (π ∘ₗ L.symm.toLinearMap) ((L.toLinearMap ∘ₗ ι) t) = 0)
    (t : E) :
    SpecialLinearGroup.congr_linearEquiv L (datumElt ι π h t) =
      datumElt (L.toLinearMap ∘ₗ ι) (π ∘ₗ L.symm.toLinearMap) h' t := by
  apply SpecialLinearGroup.ext
  intro v
  simp only [SpecialLinearGroup.congr_linearEquiv_apply_apply, datumElt_apply,
    LinearMap.comp_apply, map_add, LinearEquiv.apply_symm_apply]
  rfl


theorem map_datumRoot_congr (L : V ≃ₗ[k] V') (ι : E →ₗ[k] V) (π : V →ₗ[k] E)
    (h : ∀ t, π (ι t) = 0) (h' : ∀ t, (π ∘ₗ L.symm.toLinearMap) ((L.toLinearMap ∘ₗ ι) t) = 0) :
    (datumRoot ι π h).map (SpecialLinearGroup.congr_linearEquiv L).toMonoidHom =
      datumRoot (L.toLinearMap ∘ₗ ι) (π ∘ₗ L.symm.toLinearMap) h' := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_datumRoot_iff, mem_datumRoot_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← congr_datumElt L ι π h h' t]
    have hcong := congrArg (SpecialLinearGroup.congr_linearEquiv L) ht
    rw [MulEquiv.apply_symm_apply] at hcong
    exact hcong
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    apply (SpecialLinearGroup.congr_linearEquiv L).injective
    rw [congr_datumElt L ι π h h' t, ht, MulEquiv.apply_symm_apply]

end CFSG.LinearAlgebra.RootGroupSL
