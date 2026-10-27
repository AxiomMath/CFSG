module

public import Mathlib.Algebra.Group.Subgroup.Basic

public section

namespace CFSG

theorem exists_surjective_range_of_ker_le {A Q Y : Type*} [Group A] [Group Q] [Group Y]
    (f : A →* Q) (ψ : A →* Y) (hψ : Function.Surjective ψ) (hker : f.ker ≤ ψ.ker) :
    ∃ ψ' : f.range →* Y, Function.Surjective ψ' := by
  have hker' : f.rangeRestrict.ker ≤ ψ.ker := by rwa [MonoidHom.ker_rangeRestrict]
  refine ⟨MonoidHom.liftOfSurjective f.rangeRestrict f.rangeRestrict_surjective ⟨ψ, hker'⟩,
    fun y => ?_⟩
  obtain ⟨a, rfl⟩ := hψ y
  exact ⟨f.rangeRestrict a, MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ψ, hker'⟩ a⟩

end CFSG
