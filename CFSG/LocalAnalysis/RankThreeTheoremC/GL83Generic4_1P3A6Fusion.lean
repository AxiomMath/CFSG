module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6fus_le_centralizer_of_wc {P : Sylow 3 G} {x : G} (hxP : x ∈ (P : Subgroup G))
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hwc : LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G))) :
    (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G)
  by_contra hPC
  have : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
  have hlt : Q.subgroupOf (P : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hPC ?_
    rw [subgroupOf_eq_top] at htop
    exact htop.trans inf_le_right
  obtain ⟨n, hnN, hnQ⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hxQ : x ∈ Q := ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩
  have hconj : (n : G) * x * (n : G)⁻¹ ∈ Q := by
    have h := (mem_normalizer_iff.mp hnN ⟨x, hxP⟩).mp (mem_subgroupOf.mpr hxQ)
    rw [mem_subgroupOf] at h
    simpa using h
  have hmap : (zpowers x).map (MulAut.conj (n : G)).toMonoidHom ≤ Q := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    simpa using hconj
  have hmem : (n : G) * x * (n : G)⁻¹ ∈ zpowers x := by
    have h := hwc n hmap
    rw [MonoidHom.map_zpowers] at h
    rw [← h]
    simp
  obtain ⟨k, hk⟩ := P.isPGroup' n
  have hk' : (n : G) ^ (3 ^ k) = 1 := by
    simpa using congrArg Subtype.val hk
  have heq := p34_conj_eq_of_pow hx1 hx3 hk' hmem
  refine hnQ (mem_subgroupOf.mpr ⟨n.2, mem_centralizer_singleton_iff.mpr ?_⟩)
  calc (n : G) * x = (n : G) * x * (n : G)⁻¹ * (n : G) := by group
    _ = x * (n : G) := by rw [heq]

end CFSG.LocalAnalysis.RankThreeTheoremC
