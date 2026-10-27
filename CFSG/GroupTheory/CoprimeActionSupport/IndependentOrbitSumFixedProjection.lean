module

public import Mathlib.RepresentationTheory.Basic

public section


namespace CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitSumFixedProjection


theorem exists_fixed_projection {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    {S : Type*} [Group S] [Finite S] {I : Type*} [MulAction S I]
    (σ : Representation F S V) (U : I → Submodule F V) (hind : iSupIndep U)
    (hmap : ∀ (s : S) (i : I), (U i).map (σ s) = U (s • i))
    (i : I) (w : V) (hw : w ∈ U i) (hw0 : w ≠ 0)
    (hstab : ∀ s : S, s • i = i → σ s w = w) :
    ∃ v : V, (∀ s : S, σ s v = v) ∧ v - w ∈ ⨆ j ∈ {j : I | j ≠ i}, U j := by
  classical
  have := Fintype.ofFinite S
  set T : Finset V := Finset.univ.image (fun s : S => σ s w) with hT
  have hmemT : ∀ u, u ∈ T ↔ ∃ s : S, σ s w = u := by
    intro u; simp [hT]
  have hwT : w ∈ T := (hmemT w).2 ⟨1, by simp⟩
  refine ⟨∑ u ∈ T, u, ?_, ?_⟩
  · intro t
    rw [map_sum]
    refine Finset.sum_nbij (σ t) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro a ha
      obtain ⟨s, rfl⟩ := (hmemT a).1 ha
      exact (hmemT _).2 ⟨t * s, by simp [map_mul]⟩
    · intro a _ b _ h
      have := congrArg (σ t⁻¹) h
      simpa [← Module.End.mul_apply, ← map_mul] using this
    · intro b hb
      obtain ⟨s, rfl⟩ := (hmemT b).1 hb
      refine ⟨σ (t⁻¹ * s) w, (hmemT _).2 ⟨_, rfl⟩, ?_⟩
      simp [map_mul, ← Module.End.mul_apply, ← map_mul]
  · rw [← Finset.add_sum_erase T _ hwT, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun u hu => ?_
    obtain ⟨hne, hu⟩ := Finset.mem_erase.1 hu
    obtain ⟨s, rfl⟩ := (hmemT u).1 hu
    have hsi : s • i ≠ i := fun h => hne (hstab s h)
    have : σ s w ∈ U (s • i) := by
      rw [← hmap]; exact ⟨w, hw, rfl⟩
    exact (Submodule.mem_iSup_of_mem (s • i) (Submodule.mem_iSup_of_mem hsi this))


end CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitSumFixedProjection
