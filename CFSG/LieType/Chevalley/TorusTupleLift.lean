module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem exists_rootDiagUnitHom_comp_eq
    {τ : Tag} {K : Type} [Field K] {G : Type*} [Group G]
    (φ : G →* ModGL τ K) (hφ : ∀ g, φ g ∈ torusGroup τ K) :
    ∃ β : G →* (Fin τ.rank → Kˣ), (rootDiagUnitHom τ K).comp β = φ := by
  have hr : ∀ g, φ g ∈ (rootDiagUnitHom τ K).range := fun g => by
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hφ g)
    exact ⟨b, hb.symm⟩
  have hinj : Function.Injective (rootDiagUnitHom τ K) := rootDiagUnit_injective
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (φ.codRestrict _ hr), ?_⟩
  ext g : 1
  exact congrArg Subtype.val ((MonoidHom.ofInjective hinj).apply_symm_apply (φ.codRestrict _ hr g))

end CFSG.LieType.Chevalley

end
