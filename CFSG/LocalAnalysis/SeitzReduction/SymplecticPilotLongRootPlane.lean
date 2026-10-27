module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.E6Pilot (IsAutConjIn)

variable {K : Type} [Field K]

theorem spCompl12_zero_eq_longRootSp2 : spCompl12 K 0 = longRootSp2 K 3 0 := by
  rw [spCompl12_eq_suppGroup, longRootSp2_eq_suppGroup]
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, OffPQ]
  rcases t with x | x <;> fin_cases x <;> simp [mem_coords]

theorem isAutConjIn_spCompl12_zero :
    IsAutConjIn (spCompl12 K 0) (longRootSp2 K 3 0) := by
  intro ι
  refine ⟨1, one_mem _, ?_⟩
  rw [← spCompl12_zero_eq_longRootSp2, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
    ι.surjective, ← MonoidHom.range_eq_map, Subgroup.range_subtype, map_one]
  ext x
  simp

end CFSG.SeitzReduction.SymplecticPilot
