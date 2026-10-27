module

public import CFSG.LocalAnalysis.ComponentClassification.CanonicalPrimeComponentLift
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

open CFSG CFSG.LocalCores

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem pLayer_characteristic : (pLayer G p).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.2 fun ϕ => ?_
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport p Fact.out
    ϕ).1 L).1 hL)

theorem layer_quotient_le_map_pLayer :
    layer (G ⧸ pPrimeCore p G) ≤ (pLayer G p).map (QuotientGroup.mk' (pPrimeCore p G)) := by
  refine sSup_le fun K hK => ?_
  obtain ⟨hL, hLK, -, -⟩ := (canonical_prime_component_lift (X := G) p).1 K hK
  calc K = (canonicalPrimeLift p K).map (QuotientGroup.mk' (pPrimeCore p G)) := hLK.symm
    _ ≤ _ := Subgroup.map_mono (le_sSup hL)

theorem solvable_prime_complement_core_perfect_layer_lift
    (hR : Group.IsSolvable (pPrimeCore p G)) {A : Subgroup G} (hAp : Group.IsPerfect A)
    (hA : A.map (QuotientGroup.mk' (pPrimeCore p G)) ≤ layer (G ⧸ pPrimeCore p G)) :
    A ≤ pLayer G p := by
  have := pLayer_characteristic (G := G) (p := p)
  have hAVR : A ≤ pLayer G p ⊔ pPrimeCore p G := by
    have h := Subgroup.map_le_iff_le_comap.1 (hA.trans layer_quotient_le_map_pLayer)
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
  have himage : A.map (QuotientGroup.mk' (pLayer G p)) ≤
      (pPrimeCore p G).map (QuotientGroup.mk' (pLayer G p)) := by
    have h := Subgroup.map_mono (f := QuotientGroup.mk' (pLayer G p)) hAVR
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge,
      bot_sup_eq] at h
  have hsolvR : Group.IsSolvable ((pPrimeCore p G).map (QuotientGroup.mk' (pLayer G p))) := by
    have := hR
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (pLayer G p)).subgroupMap_surjective (pPrimeCore p G))
  have hsolvA : Group.IsSolvable (A.map (QuotientGroup.mk' (pLayer G p))) := by
    have := hsolvR
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective himage)
  have := hAp
  have hperfA : Group.IsPerfect (A.map (QuotientGroup.mk' (pLayer G p))) :=
    Group.IsPerfect.map (QuotientGroup.mk' (pLayer G p))
  have hbot : A.map (QuotientGroup.mk' (pLayer G p)) = ⊥ := by
    by_contra hne
    have : Nontrivial (A.map (QuotientGroup.mk' (pLayer G p))) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable _ hsolvA
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

end CFSG.ComponentClassification.CatalogueBPrimeJoin
