module

public import CFSG.CGT.PushingUpLit.SolKNA.Residue
import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome sylowImg IsCommSubgroup isPGroup_sylowImg
  SolomonTimmesfeldMainNonAbelian)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)

section Rank

variable {G : Type} [Group G] [Finite G]

theorem pRank_coe_eq (H : Subgroup G) : CFSG.pRank 2 ↥H = CFSG.Open.pRank 2 H :=
  CFSG.SectionRank.pRank_coe_eq_openPRank 2 H

omit [Finite G] in
theorem isCommSubgroup_of_isCyclic {H : Subgroup G} (h : IsCyclic ↥H) : IsCommSubgroup H :=
  fun a ha b hb => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥H) ⟨b, hb⟩)

theorem isCyclic_or_isQuaternionTwoGroup {H : Subgroup G} (h2 : IsPGroup 2 ↥H)
    (hrk : CFSG.Open.pRank 2 H ≤ 1) : IsCyclic ↥H ∨ IsQuaternionTwoGroup H := by
  rw [← pRank_coe_eq] at hrk
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification Nat.prime_two
    h2).mp hrk with hcyc | ⟨-, n, hn, hqe⟩
  · exact Or.inl hcyc
  · exact Or.inr ⟨n, hn, hqe⟩

end Rank

theorem nonAbelian_of_split (hq : SolomonTimmesfeldMainQuaternion)
    (hm : SolomonTimmesfeldMainRankGe2) : SolomonTimmesfeldMainNonAbelian := by
  intro G _ _ hKP hs hna K hK hM hF R hnc
  by_cases hrk : 2 ≤ CFSG.Open.pRank 2 (sylowImg R)
  · exact hm G hKP hs hna K hK hM hF R hnc hrk
  · refine hq G hKP hs hna K hK hM hF R ?_
    rcases isCyclic_or_isQuaternionTwoGroup (isPGroup_sylowImg R) (by omega) with hcyc | hqt
    · exact absurd (isCommSubgroup_of_isCyclic hcyc) hnc
    · exact hqt

end CFSG.CGT.PushingUpLit.SolKNA
