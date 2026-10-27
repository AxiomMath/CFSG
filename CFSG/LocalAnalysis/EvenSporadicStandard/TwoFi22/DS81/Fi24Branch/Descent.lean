module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

theorem exists_descent {G G' X : Type} [Group G] [Group G'] [Group X] (f : G →* G')
    (hf : Function.Surjective f) (g : G →* X) (hker : f.ker ≤ g.ker) :
    ∃ h : G' →* X, (∀ x, h (f x) = g x) ∧ h.ker = g.ker.map f := by
  obtain ⟨h, hh⟩ : ∃ h : G' →* X, ∀ x, h (f x) = g x :=
    ⟨MonoidHom.liftOfSurjective f hf ⟨g, hker⟩, fun x =>
      MonoidHom.liftOfRightInverse_comp_apply f _ (Function.rightInverse_surjInv hf)
        ⟨g, hker⟩ x⟩
  refine ⟨h, hh, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := hf y
  rw [MonoidHom.mem_ker, hh, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x', hx', hfx⟩
    have hmem : x'⁻¹ * x ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfx, inv_mul_cancel]
    have h1 : g (x'⁻¹ * x) = 1 := hker hmem
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp hx', inv_one, one_mul] at h1
    exact h1

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
