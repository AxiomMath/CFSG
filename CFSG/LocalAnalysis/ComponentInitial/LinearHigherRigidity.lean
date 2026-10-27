module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem apply_smul_eq_smul_apply (η : Ω → Subgroup G) (hη : Function.Injective η)
    (hequiv : ∀ (g : G) (ω : Ω), η (g • ω) = (η ω).map (MulAut.conj g).toMonoidHom)
    (γ : MulAut G) (f : Ω → Ω) (hγ : ∀ ω, (η ω).map γ.toMonoidHom = η (f ω)) (g : G)
    (ω : Ω) : f (g • ω) = γ g • f ω := by
  apply hη
  rw [← hγ (g • ω), hequiv g ω, hequiv (γ g) (f ω), ← hγ ω, Subgroup.map_map,
    Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem equivariant_subgroup_rigidity [FaithfulSMul G Ω] (η : Ω → Subgroup G)
    (hη : Function.Injective η)
    (hequiv : ∀ (g : G) (ω : Ω), η (g • ω) = (η ω).map (MulAut.conj g).toMonoidHom)
    (α β : MulAut G) (f : Ω → Ω) (hf : Function.Bijective f)
    (hα : ∀ ω, (η ω).map α.toMonoidHom = η (f ω))
    (hβ : ∀ ω, (η ω).map β.toMonoidHom = η (f ω)) : α = β := by
  ext g
  refine eq_of_smul_eq_smul (α := Ω) fun ω => ?_
  obtain ⟨ω', rfl⟩ := hf.2 ω
  rw [← apply_smul_eq_smul_apply η hη hequiv α f hα, apply_smul_eq_smul_apply η hη hequiv β f hβ]

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
