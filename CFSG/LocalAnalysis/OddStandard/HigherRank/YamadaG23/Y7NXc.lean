module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem y7n_isSylowIn_top_of_normalizer_le {K P1 : Subgroup G}
    (hsyl : IsSylowIn 2 (normalizer (K : Set G)) P1)
    (hN : normalizer (P1 : Set G) ≤ normalizer (K : Set G)) : IsSylowIn 2 ⊤ P1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP1p : IsPGroup 2 P1 := hsyl.2.1
  obtain ⟨Q, hP1Q⟩ := hP1p.exists_le_sylow
  have hP1eqQ : P1 = (Q : Subgroup G) := by
    by_contra hne
    have hHtop : P1.subgroupOf (Q : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      exact hne (le_antisymm hP1Q (Subgroup.subgroupOf_eq_top.mp htop))
    have hnc : NormalizerCondition ↥Q := by
      haveI : Group.IsNilpotent ↥Q := Q.isPGroup'.isNilpotent
      exact Group.normalizerCondition_of_isNilpotent
    have hHnorm : P1.subgroupOf (Q : Subgroup G) <
        normalizer (P1.subgroupOf (Q : Subgroup G)) := hnc _ hHtop
    obtain ⟨y, hyn, hyH⟩ := SetLike.not_le_iff_exists.mp (not_le_of_gt hHnorm)
    let x : G := (y : G)
    have hyQ : x ∈ (Q : Subgroup G) := y.2
    have hxN : x ∈ normalizer (P1 : Set G) := by
      have hy' : y ∈ (normalizer P1).subgroupOf (Q : Subgroup G) := by
        rw [Subgroup.subgroupOf_normalizer_eq hP1Q]
        exact hyn
      exact Subgroup.mem_subgroupOf.mp hy'
    let R : Subgroup G := (Q : Subgroup G) ⊓ normalizer (P1 : Set G)
    have hR2 : IsPGroup 2 R := Q.isPGroup'.to_le inf_le_left
    have hRK : R ≤ normalizer (K : Set G) := le_trans inf_le_right hN
    have hP1R : P1 ≤ R := fun _ hx => ⟨hP1Q hx, Subgroup.le_normalizer hx⟩
    have hxR : x ∈ R := ⟨hyQ, hxN⟩
    have hxP1 : x ∈ P1 := (sylowIn_eq_of_le hsyl hR2 hRK hP1R) ▸ hxR
    exact hyH (Subgroup.mem_subgroupOf.mpr hxP1)
  refine ⟨le_top, hP1p, ?_⟩
  rw [Subgroup.relIndex_top_right, hP1eqQ]
  exact Q.not_dvd_index

end CFSG.OddStandard.HigherRank.YamadaG23
