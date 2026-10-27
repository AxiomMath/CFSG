module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

theorem l16a_exists_oddCore_mul [Finite G] {D X S : Subgroup G} (hS : IsSylow2Of S X)
    (hDX : D ≤ X) (hXN : X ≤ normalizer (D : Set G))
    (hcyc : ∀ P : Sylow 2 ↥D, IsCyclic ↥(P : Subgroup ↥D)) :
    ∀ y ∈ D, ∃ o ∈ oddCoreIn D, ∃ s ∈ S ⊓ D, y = o * s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ D) D :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mpr hS).inf_of_le_normalizer hDX hXN
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  obtain ⟨N, hNn, hNc⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two Q (hcyc Q)
  have hNodd : Odd (Nat.card N) := by
    have hQnd : ¬ 2 ∣ (Q : Subgroup ↥D).index := Q.not_dvd_index
    rw [← hNc.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hQnd)
  have hNle : N.map D.subtype ≤ oddCoreIn D := by
    refine le_oddCoreIn_of_normal (Subgroup.map_subtype_le N) ?_ ?_
    · have h : (N.map D.subtype).subgroupOf D = N :=
        Subgroup.comap_map_eq_self_of_injective D.subtype_injective N
      rw [h]
      exact hNn
    · rw [Subgroup.card_map_of_injective D.subtype_injective]
      exact hNodd
  intro y hy
  obtain ⟨⟨⟨n, hn⟩, ⟨q, hq⟩⟩, hnq⟩ := hNc.2 ⟨y, hy⟩
  refine ⟨(n : G), hNle (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩), (q : G), ?_, ?_⟩
  · have hq' : q ∈ (S ⊓ D).subgroupOf D := hQ ▸ hq
    exact Subgroup.mem_subgroupOf.mp hq'
  · simpa using (congrArg Subtype.val hnq).symm

end CFSG.OddStandard.SmallF3.Omega
