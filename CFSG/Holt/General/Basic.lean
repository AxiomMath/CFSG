module

public import CFSG.Holt.Basic

public section

namespace CFSG.Holt.General

open MulAction CFSG.Holt

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {z : G} {α : Ω}

theorem isPretransitive_of_le_of_normal_subgroupOf [Finite Ω] {K L : Subgroup G} (hLK : L ≤ K)
    (hL : (L.subgroupOf K).Normal) [IsPretransitive K Ω] (hz : orderOf z = 2) (hzL : z ∈ L)
    (hα : ∀ ω : Ω, z • ω = ω ↔ ω = α) : IsPretransitive L Ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply isPretransitive_of_forall_exists_fixSet_eq_singleton 2
  intro δ
  obtain ⟨k, rfl⟩ := exists_smul_eq K α δ
  have hdL : (k : G) * z * (k : G)⁻¹ ∈ L :=
    Subgroup.mem_subgroupOf.mp (hL.conj_mem ⟨z, hLK hzL⟩ (Subgroup.mem_subgroupOf.mpr hzL) k)
  let d : L := ⟨(k : G) * z * (k : G)⁻¹, hdL⟩
  have hd : orderOf d = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_eq_of_isConj (isConj_iff.mpr ⟨(k : G), rfl⟩)).symm.trans hz
  refine ⟨Subgroup.zpowers d, isPGroup_zpowers_of_orderOf_eq_two hd, ?_⟩
  ext ω
  rw [fixSet_zpowers, mem_fixedBy, Set.mem_singleton_iff, Subgroup.smul_def]
  exact conj_smul_eq_self_iff hα (k : G) ω

end CFSG.Holt.General
