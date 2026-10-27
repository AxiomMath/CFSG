module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight
public import CFSG.ClassicalInvolution.SubnormalClosure.Basic

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ComponentClassification

theorem exists_isClassical2A7_of_witness {F : Type} [Group F] [Finite F] {z : F}
    (hz : orderOf z = 2) {K : Subgroup F} (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer ({z} : Set F))) (hw : A7Witness K) :
    ∃ L : Subgroup F, IsClassical2A7 ⊤ L z := by
  set X : Subgroup F := Subgroup.centralizer ({z} : Set F) with hX
  have hKX : K ≤ X := isSubnormal_le hK
  have hzX : z ∈ X := hKX hzK
  have hKsub : IsSubnormal (K.subgroupOf X) ⊤ := by
    have := isSubnormal_subgroupOf hK X
    rwa [Subgroup.subgroupOf_self] at this
  have eKX : K.subgroupOf X ≃* K := Subgroup.subgroupOfEquivOfLe hKX
  have hwX : A7Witness (K.subgroupOf X) := A7Witness.of_mulEquiv eKX.symm hw
  obtain ⟨L, hLle, hL2, hmap⟩ := exists_isTwoComponent_le (K.subgroupOf X) hKsub hwX.1
  have hLsub : IsSubnormal L ⊤ := hL2.1
  have hz'L : (⟨z, hzX⟩ : X) ∈ L :=
    mem_of_orderOf_eq_two_of_map_eq hLle hLsub hKsub hmap (Subgroup.mem_subgroupOf.mpr hzK)
      (by rw [Subgroup.orderOf_mk]; exact hz)
  obtain ⟨e2⟩ := nonempty_oddCoreQuotientEquiv_of_map_eq hLsub hKsub hmap
  have hwL : A7Witness L := A7Witness.of_quotientEquiv e2.symm hwX
  have hperf : Group.IsPerfect L := ⟨TwoComponents.perfect hL2⟩
  refine ⟨L.map X.subtype, ⟨?_, ⟨⟨z, hzX⟩, hz'L, rfl⟩, ?_, ?_, ?_⟩⟩
  · exact hz
  · exact Group.IsPerfect.map X.subtype
  · have h1 := Components.chain_map X.subtype hLsub
    rw [Subgroup.map_top, Subgroup.range_subtype] at h1
    rw [top_inf_eq]
    exact h1
  · exact A7Witness.of_mulEquiv (L.equivMapOfInjective X.subtype X.subtype_injective) hwL

end CFSG.ClassicalInvolution.Hat2A7
