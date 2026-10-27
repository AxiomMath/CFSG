module

public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondenceTools

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelLQ

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem pLayer_map_quotient_of_odd {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) :
    (pLayer X 2).map (QuotientGroup.mk' N) = pLayer (X ⧸ N) 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ComponentClassification.UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel
    (p := 2) (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) ?_
  rw [QuotientGroup.ker_mk']
  intro h2
  obtain ⟨k, hk⟩ := hN
  obtain ⟨m, hm⟩ := h2
  omega

theorem pLayerOf_eq_map {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) :
    pLayerOf p H = (pLayer ↥H p).map H.subtype := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    obtain ⟨hLH, hL2⟩ := hL
    rw [← Subgroup.map_subgroupOf_eq_of_le hLH]
    exact Subgroup.map_mono (le_sSup hL2)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨?_, ?_⟩
    · rintro _ ⟨m, -, rfl⟩
      exact m.2
    · have : (M.map H.subtype).subgroupOf H = M :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective M
      rw [this]
      exact hM

end CFSG.GH74.GLS.Stage2.Final.ModelLQ
