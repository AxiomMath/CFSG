module

public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V]

theorem twisted_eq_zero_of_apply_eq_zero (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    (F : N →+ V) (ρ : Gsp BN →* (V ≃ₗ[K] V))
    (hρ : ∀ (g : Gsp BN) (x : N), F (g.app x) = ρ g (F x))
    (hF0 : F ≠ 0) {x : N} (hx : x ≠ 0) (hFx : F x = 0) : False := by
  apply hF0
  refine AddMonoidHom.ext fun y => ?_
  by_cases hy : y = 0
  · simp [hy]
  · obtain ⟨g, rfl⟩ := CFSG.ClassicalGroups.Symplectic.exists_gsp_apply_eq hBN hBNnd hx hy
    rw [hρ, hFx, map_zero, AddMonoidHom.zero_apply]

theorem injective_of_twisted_equivariant (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    (σ : K ≃+* K) (F : N →+ V) (_hF : ∀ (c : K) (x : N), F (c • x) = σ c • F x)
    (ρ : Gsp BN →* (V ≃ₗ[K] V)) (hρ : ∀ (g : Gsp BN) (x : N), F (g.app x) = ρ g (F x))
    (hF0 : F ≠ 0) : Function.Injective F := by
  refine (injective_iff_map_eq_zero F).2 fun x hFx => ?_
  by_contra hx
  exact twisted_eq_zero_of_apply_eq_zero hBN hBNnd F ρ hρ hF0 hx hFx

theorem twisted_natural_irreducible (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    (σ : K ≃+* K) (F : N →+ V) (hF : ∀ (c : K) (x : N), F (c • x) = σ c • F x)
    (ρ : Gsp BN →* (V ≃ₗ[K] V)) (hρ : ∀ (g : Gsp BN) (x : N), F (g.app x) = ρ g (F x))
    (_hF0 : F ≠ 0) :
    (∀ w ∈ Submodule.span K (Set.range F), ∃ x, F x = w) ∧
      ∀ U : Submodule K V, U ≠ ⊥ → U ≤ Submodule.span K (Set.range F) →
        (∀ (g : Gsp BN), ∀ u ∈ U, ρ g u ∈ U) → U = Submodule.span K (Set.range F) := by
  let W : Submodule K V :=
    { carrier := Set.range F
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, map_add F x y⟩
      zero_mem' := ⟨0, map_zero F⟩
      smul_mem' := by
        rintro c _ ⟨x, rfl⟩
        refine ⟨σ.symm c • x, ?_⟩
        rw [hF, RingEquiv.apply_symm_apply] }
  have hspan : Submodule.span K (Set.range F) ≤ W := Submodule.span_le.mpr fun v hv => hv
  refine ⟨fun w hw => ?_, fun U hU0 hUle hUinv => ?_⟩
  · have hw' : w ∈ Set.range F := hspan hw
    exact hw'
  · refine le_antisymm hUle (Submodule.span_le.mpr ?_)
    rintro _ ⟨y, rfl⟩
    by_cases hy : y = 0
    · rw [hy, map_zero]
      exact U.zero_mem
    · obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have hu : u ∈ Set.range F := hspan (hUle huU)
      obtain ⟨x, rfl⟩ := hu
      have hx : x ≠ 0 := by
        rintro rfl
        exact hu0 (map_zero F)
      obtain ⟨g, rfl⟩ := CFSG.ClassicalGroups.Symplectic.exists_gsp_apply_eq hBN hBNnd hx hy
      rw [hρ]
      exact hUinv g _ huU

end CFSG.ClassicalGroups.Alternating
