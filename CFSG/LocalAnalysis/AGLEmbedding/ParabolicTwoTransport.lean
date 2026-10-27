module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelNormalizers

public section

namespace CFSG.AGLEmbedding

theorem IsParabolicTwo.subgroupOf_top {X : Type*} [Group X] {L J : Subgroup X}
    (h : CFSG.AGLEmbedding.IsParabolicTwo L J) :
    CFSG.AGLEmbedding.IsParabolicTwo (⊤ : Subgroup ↥L) (J.subgroupOf L) := by
  obtain ⟨-, T, hT, hNJ⟩ := h
  refine ⟨le_top, T.subgroupOf L, isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT, ?_⟩
  intro x hx
  rw [Subgroup.mem_inf] at hx
  refine Subgroup.mem_subgroupOf.mpr (hNJ (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩))
  exact coe_mem_normalizer_of_subgroupOf hT.1 hx.2

theorem IsParabolicTwo.map_top_of_surjective_of_odd_ker {A B : Type*} [Group A] [Finite A]
    [Group B] {J : Subgroup A}
    (hpar : CFSG.AGLEmbedding.IsParabolicTwo (⊤ : Subgroup A) J)
    (φ : A →* B) (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker)) :
    CFSG.AGLEmbedding.IsParabolicTwo (⊤ : Subgroup B) (J.map φ) := by
  obtain ⟨-, T, hT, hNJ⟩ := hpar
  refine ⟨le_top, T.map φ, isSylowTwoOf_map_top_of_surjective hT hφ, ?_⟩
  intro x hx
  rw [Subgroup.mem_inf] at hx
  rw [← CFSG.ComponentClassification.OddKernelNormalizers.image φ hφ hodd T hT.2.1] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx.2
  exact Subgroup.mem_map_of_mem φ (hNJ (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top y, hy⟩))

end CFSG.AGLEmbedding

end
