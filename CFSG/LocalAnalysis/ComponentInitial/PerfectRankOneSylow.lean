module

public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.ComponentInitial

theorem perfect_rank_one_Sylow_quaternion {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (hG : Even (Nat.card G)) (hr : CFSG.pRank 2 G ≤ 1) (S : Sylow 2 G) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty (S ≃* QuaternionGroup (2 ^ (n - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.pRank 2 (S : Subgroup G) ≤ 1 := by
    rw [(CFSG.SectionRank.pRank_sylow S).2]
    exact hr
  rcases (pgroup_rank_one_classification Nat.prime_two S.isPGroup').1 hS with hcyc | ⟨-, n, hn, he⟩
  · exact absurd hcyc (perfect_even_sylow_noncyclic hG S)
  · exact ⟨n, hn, he⟩

end CFSG.LocalAnalysis.ComponentInitial
