module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowIn_of_le {K U : Subgroup G} (hUK : U ≤ K) (hU : IsPGroup 2 U) :
    ∃ 𝒮 : Subgroup G, IsSylowIn 2 𝒮 K ∧ U ≤ 𝒮 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (U.subgroupOf K) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUK).symm
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  refine ⟨(P : Subgroup K).map K.subtype, ⟨Subgroup.map_subtype_le _, ?_, ?_⟩, ?_⟩
  · exact P.2.of_equiv (Subgroup.equivMapOfInjective _ _ K.subtype_injective)
  · have h : ((P : Subgroup K).map K.subtype).subgroupOf K = P := by
      change ((P : Subgroup K).map K.subtype).comap K.subtype = P
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    change ¬ 2 ∣ (((P : Subgroup K).map K.subtype).subgroupOf K).index
    rw [h]
    exact P.not_dvd_index
  · intro u hu
    have : (⟨u, hUK hu⟩ : K) ∈ (U.subgroupOf K) := hu
    exact ⟨⟨u, hUK hu⟩, hP' this, rfl⟩

theorem isPGroup_pCoreOf (H : Subgroup G) : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) := by
  rw [CFSG.Open.pCoreOf]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype

theorem eq_of_forall_normalizes {𝒯 T : Subgroup G} (h𝒯 : IsPGroup 2 𝒯) (hT : T ≤ 𝒯)
    (hN : ∀ n ∈ 𝒯, (∀ x ∈ T, n * x * n⁻¹ ∈ T) → n ∈ T) : T = 𝒯 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥𝒯 := h𝒯.isNilpotent
  have hnc : NormalizerCondition ↥𝒯 := Group.normalizerCondition_of_isNilpotent
  have htop : T.subgroupOf 𝒯 = ⊤ := by
    by_contra hne
    have hlt : T.subgroupOf 𝒯 < ⊤ := lt_of_le_of_ne le_top hne
    obtain ⟨n, hnN, hnT⟩ := SetLike.exists_of_lt (hnc (T.subgroupOf 𝒯) hlt)
    have hmem : (n : G) ∈ T := by
      refine hN (n : ↥𝒯) n.2 ?_
      intro x hx
      have hx' : (⟨x, hT hx⟩ : ↥𝒯) ∈ T.subgroupOf 𝒯 := hx
      have hconj : n * (⟨x, hT hx⟩ : ↥𝒯) * n⁻¹ ∈ T.subgroupOf 𝒯 :=
        (Subgroup.mem_normalizer_iff.mp hnN ⟨x, hT hx⟩).mp hx'
      simpa [Subgroup.mem_subgroupOf] using hconj
    exact hnT ((Subgroup.mem_subgroupOf).mpr hmem)
  have hle : 𝒯 ≤ T := (Subgroup.subgroupOf_eq_top).mp htop
  exact le_antisymm hT hle

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
