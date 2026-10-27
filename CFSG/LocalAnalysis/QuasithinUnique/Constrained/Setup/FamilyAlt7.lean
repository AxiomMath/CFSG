module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAlt7Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.Milestones.AT_alternating_automorphism_permutation

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.QuasithinUnique.Setup.X6

theorem twoGeneratingSylowOvergroups_alt_seven :
    TwoGeneratingSylowOvergroups (alternatingGroup (Fin 7)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro D hD R hR
  have hU : CFSG.ABGLocalTools.IsSylowOf 2 U7' ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, isPGroup_U7', ?_⟩
    rw [Subgroup.relIndex_top_right, index_U7']
    norm_num
  have hZ : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  refine automorphism_invariant_generating_Sylow_overgroups_lift hZ hU Q71_not_normal
    Q72_not_normal Q71_sup_Q72 ?_ hD (isSylowTwoOf_iff_isSylowOf.1 hR)
  intro α hα
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation (Or.inr le_rfl) α
  exact inv_of_conj α σ hσ hα

end CFSG.QuasithinUnique.Setup.Family
