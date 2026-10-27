module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FStdDefs
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.Open (standardComponentIsStandard)
open CFSG.DisconnectedInvolutionGraph.Helpers (NoCommutingDistinctInvolutions
  rank_one_two_cyclic_or_quaternion)
open CFSG.ComponentClassification.StandardRecognition (ClassicalInvolutionTheoremModels
  quaternion_standard_recognition)

theorem s7f_quaternion_of_rank_le_one {P : Type*} [Group P] [Finite P]
    (hrk : ¬ 2 ≤ CFSG.pRank 2 P) (S : Sylow 2 P) (hS : ¬ IsCyclic (S : Subgroup P)) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty ((S : Subgroup P) ≃* QuaternionGroup (2 ^ (n - 2))) := by
  have hno : NoCommutingDistinctInvolutions (S : Subgroup P) := by
    intro a b hab
    by_contra hne
    refine hrk (s7f_two_le_pRank_of_commute (u := (a.1 : P)) (v := (b.1 : P)) ?_ ?_ ?_ ?_)
    · rw [Subgroup.orderOf_coe]
      exact a.2
    · rw [Subgroup.orderOf_coe]
      exact b.2
    · exact congrArg Subtype.val hab
    · intro h
      exact hne (Subtype.ext (Subtype.ext h))
  rcases rank_one_two_cyclic_or_quaternion S.isPGroup' hno with h | ⟨e, he, ⟨φ⟩⟩
  · exact absurd h hS
  · refine ⟨e + 2, by omega, ⟨?_⟩⟩
    rw [Nat.add_sub_cancel]
    exact φ.symm

variable {G : Type} [Group G]

theorem s7f_oddLie_or_mathieu (hCIT : ClassicalInvolutionTheoremModels) [Finite G]
    [IsSimpleGroup G] {X : Subgroup G} (hX : standardComponentIsStandard X) (hXF : InFStar X)
    (hrk : ¬ 2 ≤ pRank 2 ↥(centralizer (X : Set G)))
    (hS : ∃ S : Sylow 2 (centralizer (X : Set G)),
      ¬ IsCyclic (S : Subgroup (centralizer (X : Set G)))) :
    OddLieType G ∨ NativeSporadic.IsSporadic G .M11 ∨ NativeSporadic.IsSporadic G .M12 := by
  obtain ⟨S, hS⟩ := hS
  obtain ⟨n, hn, he⟩ := s7f_quaternion_of_rank_le_one hrk S hS
  exact quaternion_standard_recognition hCIT
    (s7f_nonab_of_quasisimple (s7f_isQuasisimple_of_inFStar hXF)) hX S hn he

end CFSG.OddStandard.SmallF3.Omega
