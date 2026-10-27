module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.PGroupNormalizerExtension
public import CFSG.Dihedral.BlueprintDefs

public section

namespace CFSG.DihedralBlueprint

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_top_of_normalizer (p : ℕ) (hp : p.Prime) (P : Subgroup G)
    (hP : IsSylowIn p P (Subgroup.normalizer (P : Set G))) : IsSylowIn p P ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨le_top, hP.2.1, ?_⟩
  intro Q _ hQ hPQ
  by_contra hne
  have hproper : P < Q := lt_of_le_of_ne hPQ (Ne.symm hne)
  obtain ⟨U, hPU, hU, hUN⟩ :=
    DisconnectedInvolutionGraph.Helpers.pgroup_strict_normalizer_extension p P Q hQ hproper
  have heq : U = P := hP.2.2 U (hUN.trans inf_le_right) hU hPU.le
  exact hPU.ne heq.symm

end CFSG.DihedralBlueprint
