module


public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.FiniteFaithfulInvariantSubspace

open Module

variable {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
  {V : Type*} [AddCommGroup V] [Module F V]

theorem exists_submodule (ρ : Representation F G V) (hρ : Function.Injective ρ) :
    ∃ W : Submodule F V, ∃ hW : (∀ g, W ≤ W.comap (ρ g)),
      Module.Finite F W ∧ Function.Injective (Representation.subrepresentation ρ W hW) := by
  classical
  have hex : ∀ g : G, ∃ v : V, g ≠ 1 → ρ g v ≠ v := by
    intro g
    by_cases hg : g = 1
    · exact ⟨0, fun h => absurd hg h⟩
    · have : ρ g ≠ 1 := fun h => hg (hρ (by rw [h, map_one]))
      obtain ⟨v, hv⟩ := not_forall.1 (fun h : ∀ v, ρ g v = v =>
        this (LinearMap.ext fun v => by simpa using h v))
      exact ⟨v, fun _ => hv⟩
  choose v hv using hex
  let W : Submodule F V := Submodule.span F (Set.range fun p : G × G => ρ p.2 (v p.1))
  have hW : ∀ g, W ≤ W.comap (ρ g) := by
    intro g
    rw [Submodule.span_le]
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show ρ g (ρ b (v a)) ∈ W
    have : ρ g (ρ b (v a)) = ρ (g * b) (v a) := by simp [map_mul]
    rw [this]
    exact Submodule.subset_span ⟨(a, g * b), rfl⟩
  refine ⟨W, hW, ?_, ?_⟩
  · have : FiniteDimensional F W :=
      FiniteDimensional.span_of_finite F (Set.finite_range _)
    infer_instance
  · rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hne
    have hmem : v g ∈ W := by
      have : ρ 1 (v g) = v g := by simp
      rw [← this]
      exact Submodule.subset_span ⟨(g, 1), rfl⟩
    apply hv g hne
    have := LinearMap.congr_fun hg ⟨v g, hmem⟩
    simpa using congrArg Subtype.val this

theorem fixed_kernel_eq_bot (ρ : Representation F G V) (W : Submodule F V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) (d : G)
    (h : LinearMap.ker (ρ d - 1) = ⊥) :
    LinearMap.ker (Representation.subrepresentation ρ W hW d - 1) = ⊥ := by
  rw [LinearMap.ker_eq_bot'] at h ⊢
  intro w hw
  apply Subtype.ext
  apply h
  have := congrArg Subtype.val hw
  simpa [sub_eq_zero] using this

end CFSG.GroupTheory.CoprimeActionSupport.FiniteFaithfulInvariantSubspace
