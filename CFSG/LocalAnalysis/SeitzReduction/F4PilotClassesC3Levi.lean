module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassesC3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAutD

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Roots


theorem C3Set_eq_c3LeviRoots : C3Set = c3LeviRoots :=
  Set.ext fun _ => mem_C3Set_iff

theorem C3Set_eq_c3PerpRoots : C3Set = c3PerpRoots :=
  Set.ext fun _ => mem_C3Set_iff.trans mem_c3PerpRoots_iff.symm

end Roots

variable {K : Type} [Field K]

section Levi


theorem C3Levi_eq_subgroupOf_rootSpan_C3Set :
    C3Levi K = (rootSpan .F4 K C3Set).subgroupOf (adjointGroup .F4 K) := by
  rw [C3Set_eq_c3LeviRoots]
  rfl

theorem c3PerpLevi_eq_rootSpan_C3Set : c3PerpLevi K = rootSpan .F4 K C3Set := by
  rw [C3Set_eq_c3PerpRoots]
  rfl

end Levi

variable [Finite K] [CharP K 2]

theorem exists_conj_mem_C3Levi {y : adjointGroup .F4 K} (hy : orderOf y = 2) :
    ∃ g : adjointGroup .F4 K, g * y * g⁻¹ ∈ C3Levi K := by
  rw [C3Levi_eq_subgroupOf_rootSpan_C3Set]
  exact exists_conj_mem_subgroupOf_C3 hy

theorem exists_conj_mem_c3PerpLevi {y : adjointGroup .F4 K} (hy : orderOf y = 2) :
    ∃ g : adjointGroup .F4 K,
      ((g * y * g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ c3PerpLevi K := by
  rw [c3PerpLevi_eq_rootSpan_C3Set]
  exact exists_conj_mem_C3 hy

theorem exists_conj_mem_C3_and_mem_centralizer_rootSL2R {y : adjointGroup .F4 K}
    (hy : orderOf y = 2) :
    ∃ g : adjointGroup .F4 K,
      ((g * y * g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K C3Set ∧
        ((g * y * g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈
          Subgroup.centralizer (rootSL2R K : Set (ModGL .F4 K)) := by
  obtain ⟨g, hg⟩ := exists_conj_mem_C3 hy
  exact ⟨g, hg, rootSpan_C3Set_le_centralizer_rootSL2R hg⟩

theorem exists_conj_mem_comap_C3Levi {L : Type*} [Group L] (e : L ≃* adjointGroup .F4 K)
    {y : L} (hy : y ^ 2 = 1) :
    ∃ l : L, l * y * l⁻¹ ∈ (C3Levi K).comap e.toMonoidHom := by
  obtain ⟨l, hl⟩ := exists_conj_mem_C3_of_mulEquiv e hy
  refine ⟨l, ?_⟩
  rw [Subgroup.mem_comap, C3Levi_eq_subgroupOf_rootSpan_C3Set, Subgroup.mem_subgroupOf]
  exact hl

end CFSG.SeitzReduction.F4Pilot
