module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem y4_sylow_of_norm {P K : Subgroup G} (hP : IsSylowIn 2 (normalizer (K : Set G)) P)
    (hK : ∀ y ∈ normalizer (P : Set G), y ∈ normalizer (K : Set G)) : IsSylowIn 2 ⊤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hPQ⟩ := hP.2.1.exists_le_sylow
  have hPeqQ : P = Q := by
    by_contra hne
    have hPq_ne_top : P.subgroupOf Q ≠ ⊤ := fun h =>
      hne (le_antisymm hPQ (Subgroup.subgroupOf_eq_top.mp h))
    have hlt : P.subgroupOf Q < (⊤ : Subgroup ↥Q) := lt_of_le_of_ne le_top hPq_ne_top
    haveI : Group.IsNilpotent ↥Q := IsPGroup.isNilpotent (p := 2) Q.isPGroup'
    have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥Q)
    obtain ⟨g, hgN, hg_notin⟩ := (SetLike.lt_iff_le_and_exists.mp (hnc _ hlt)).2
    have hgN' : (g : G) ∈ normalizer (P : Set G) := by
      refine Subgroup.mem_subgroupOf.mp ?_
      rwa [Subgroup.subgroupOf_normalizer_eq hPQ]
    have hg_notin_P : (g : G) ∉ P := fun h => hg_notin (Subgroup.mem_subgroupOf.mpr h)
    have hP'grp : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers (g : G)) :=
      IsPGroup.to_le (p := 2) Q.isPGroup' (sup_le hPQ (Subgroup.zpowers_le.mpr g.2))
    have hP'N : P ⊔ Subgroup.zpowers (g : G) ≤ normalizer (K : Set G) :=
      sup_le hP.1 (Subgroup.zpowers_le.mpr (hK (g : G) hgN'))
    have heq := sylowIn_eq_of_le hP hP'grp hP'N le_sup_left
    have hx : (g : G) ∈ P ⊔ Subgroup.zpowers (g : G) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers (g : G))
    rw [← heq] at hx
    exact hg_notin_P hx
  rw [hPeqQ]
  exact ⟨le_top, Q.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Q.not_dvd_index⟩

end CFSG.OddStandard.HigherRank.YamadaG23
