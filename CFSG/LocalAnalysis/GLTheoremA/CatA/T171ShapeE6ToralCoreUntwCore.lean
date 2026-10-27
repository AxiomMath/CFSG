module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
open scoped Pointwise

theorem exists_mem_componentRootSpan_conj_eq_of_mem_torusGroup
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L) :
    ∃ g ∈ componentRootSpan L (rootCharHom a) i,
      ∀ x ∈ componentRootSpan L (rootCharHom a) i, y * x * y⁻¹ = g * x * g⁻¹ := by
  obtain ⟨g, hg, hconj⟩ := exists_mem_rootSpan_conj_eq_of_mem_Z i
    (Subgroup.mem_sup_left hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
  refine ⟨g, ?_, hconj⟩
  have hEq : unionRootSpan L (rootCharHom a)
        ({i} : Set (KernelComponent (rootCharHom a))) =
      componentRootSpan L (rootCharHom a) i := by
    simp only [unionRootSpan, componentRootSpan, unionRoots, componentRoots, Set.mem_singleton_iff]
  rwa [hEq] at hg

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
