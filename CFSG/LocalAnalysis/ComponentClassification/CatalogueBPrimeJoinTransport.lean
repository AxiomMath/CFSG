module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem primeResidual_eq_top_of_equiv {G H : Type*} [Group G] [Group H]
    (p : ℕ) (e : G ≃* H) (hgenerated : primeResidual p G = ⊤) :
    primeResidual p H = ⊤ := by
  have h := primeResidual_map_equiv p e
  rw [hgenerated, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h
  exact h.symm

theorem quasisimple_primeCore_quotient_of_equiv {G H : Type*} [Group G] [Group H]
    (p : ℕ) (e : G ≃* H) (hquasisimple : CFSG.IsQuasisimple (G ⧸ pPrimeCore p G)) :
    CFSG.IsQuasisimple (H ⧸ pPrimeCore p H) := by
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      (QuotientGroup.congr (pPrimeCore p G) (pPrimeCore p H) e
        (pPrimeCore_map_iso p e)).symm
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasisimple))

theorem pComponent_subgroupOf_iff {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L H : Subgroup G) (hle : L ≤ H) :
    CFSG.IsPComponent p (L.subgroupOf H) ↔ (L.subgroupOf H).IsSubnormal ∧
      primeResidual p L = ⊤ ∧ CFSG.IsQuasisimple (L ⧸ pPrimeCore p L) := by
  let e := Subgroup.subgroupOfEquivOfLe hle
  constructor
  · intro hL
    obtain ⟨hsubnormal, hgenerated, hquasisimple⟩ :=
      (pComponent_iff_subnormal_generated_quasisimple p _).mp hL
    exact ⟨hsubnormal, primeResidual_eq_top_of_equiv p e hgenerated,
      quasisimple_primeCore_quotient_of_equiv p e hquasisimple⟩
  · rintro ⟨hsubnormal, hgenerated, hquasisimple⟩
    exact (pComponent_iff_subnormal_generated_quasisimple p _).mpr
      ⟨hsubnormal, primeResidual_eq_top_of_equiv p e.symm hgenerated,
        quasisimple_primeCore_quotient_of_equiv p e.symm hquasisimple⟩

theorem pComponent_restrict_overgroup {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] {L H : Subgroup G} (hL : CFSG.IsPComponent p L)
    (hle : L ≤ H) : CFSG.IsPComponent p (L.subgroupOf H) := by
  obtain ⟨hsubnormal, hgenerated, hquasisimple⟩ :=
    (pComponent_iff_subnormal_generated_quasisimple p L).mp hL
  exact (pComponent_subgroupOf_iff p L H hle).mpr
    ⟨hsubnormal.subgroupOf, hgenerated, hquasisimple⟩

theorem pComponent_extend_subnormal {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (H : Subgroup G) (hH : H.IsSubnormal)
    (L : Subgroup H) (hL : CFSG.IsPComponent p L) : CFSG.IsPComponent p (L.map H.subtype) := by
  obtain ⟨hsubnormal, hgenerated, hquasisimple⟩ :=
    (pComponent_iff_subnormal_generated_quasisimple p L).mp hL
  let e := L.equivMapOfInjective H.subtype H.subtype_injective
  exact (pComponent_iff_subnormal_generated_quasisimple p _).mpr
    ⟨hsubnormal.trans' hH, primeResidual_eq_top_of_equiv p e hgenerated,
      quasisimple_primeCore_quotient_of_equiv p e hquasisimple⟩

theorem pComponent_subnormal_overgroup_iff {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L H : Subgroup G) (hle : L ≤ H) (hH : H.IsSubnormal) :
    CFSG.IsPComponent p (L.subgroupOf H) ↔ CFSG.IsPComponent p L := by
  constructor
  · intro hL
    have h := pComponent_extend_subnormal p H hH (L.subgroupOf H) hL
    simpa only [Subgroup.map_subgroupOf_eq_of_le hle] using h
  · exact fun hL => pComponent_restrict_overgroup p hL hle

theorem p_component_overgroup_subnormal_transport {G : Type*} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (L H : Subgroup G) (hle : L ≤ H) :
    (CFSG.IsPComponent p L → CFSG.IsPComponent p (L.subgroupOf H)) ∧
      (H.IsSubnormal → CFSG.IsPComponent p (L.subgroupOf H) → CFSG.IsPComponent p L) := by
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨fun hL => pComponent_restrict_overgroup p hL hle,
    fun hH hL => (pComponent_subnormal_overgroup_iff p L H hle hH).mp hL⟩

end CFSG.ComponentClassification.CatalogueBPrimeJoin
