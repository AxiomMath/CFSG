module

public import CFSG.FeitThompson.Local.PLengthOneNormalComplementElementSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {X : Type*} [Group X]

theorem image_subtype_pElements {H : Subgroup X} (hH : pElements p X ⊆ (H : Set X)) :
    H.subtype '' pElements p H = pElements p X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := mem_pElements.1 hy
    exact mem_pElements.2 ⟨n, (Subgroup.orderOf_coe y).trans hn⟩
  · intro hx
    obtain ⟨n, hn⟩ := mem_pElements.1 hx
    have hmem : x ∈ H := hH (mem_pElements.2 ⟨n, hn⟩)
    exact ⟨⟨x, hmem⟩, mem_pElements.2
      ⟨n, (Subgroup.orderOf_coe (⟨x, hmem⟩ : H)).symm.trans hn⟩, rfl⟩

theorem pElementSubgroup_map_subtype {H : Subgroup X} (hH : pElements p X ⊆ (H : Set X)) :
    (pElementSubgroup p H).map H.subtype = pElementSubgroup p X := by
  rw [pElementSubgroup_eq_closure, pElementSubgroup_eq_closure, MonoidHom.map_closure,
    image_subtype_pElements hH]

noncomputable def pElementSubgroupEquiv {H : Subgroup X} (hH : pElements p X ⊆ (H : Set X)) :
    pElementSubgroup p H ≃* pElementSubgroup p X :=
  (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (pElementSubgroup_map_subtype hH))

variable {Y Z : Type*} [Group Y] [Group Z]

theorem IsNormalPComplement.map_mulEquiv (e : Y ≃* Z) {K : Subgroup Y}
    (h : IsNormalPComplement p K) : IsNormalPComplement p (K.map (e : Y →* Z)) := by
  refine isNormalPComplement_of (MulEquiv.normal_map_iff.2 h.normal) ?_ ?_
  · rw [Subgroup.card_map_of_injective e.injective]
    exact h.not_dvd_natCard
  · obtain ⟨n, hn⟩ := h.exists_index_eq_pow
    exact ⟨n, by rw [Subgroup.index_map_equiv, hn]⟩

theorem HasNormalPComplement.of_mulEquiv (e : Y ≃* Z) (h : HasNormalPComplement p Y) :
    HasNormalPComplement p Z :=
  let ⟨K, hK⟩ := hasNormalPComplement_iff.1 h
  hasNormalPComplement_iff.2 ⟨K.map (e : Y →* Z), hK.map_mulEquiv e⟩

theorem hasNormalPComplement_congr (e : Y ≃* Z) :
    HasNormalPComplement p Y ↔ HasNormalPComplement p Z :=
  ⟨HasNormalPComplement.of_mulEquiv e, HasNormalPComplement.of_mulEquiv e.symm⟩

theorem hasPLengthLeOne_of_pElements_subset [Finite X] [Fact p.Prime] {H : Subgroup X}
    (hH : pElements p X ⊆ (H : Set X)) (h : HasPLengthLeOne p H) : HasPLengthLeOne p X :=
  hasPLengthLeOne_iff_hasNormalPComplement.2
    ((hasPLengthLeOne_iff_hasNormalPComplement.1 h).of_mulEquiv (pElementSubgroupEquiv hH))

theorem pElements_subset_iff_pElementSubgroup_le {H : Subgroup X} :
    pElements p X ⊆ (H : Set X) ↔ pElementSubgroup p X ≤ H := pElementSubgroup_le_iff.symm

theorem HasPLengthLeOne.of_normal_of_pElements_subset [Finite X] [Fact p.Prime] {H : Subgroup X}
    [H.Normal] (hH : pElements p X ⊆ (H : Set X)) (h : HasPLengthLeOne p H) :
    HasPLengthLeOne p X :=
  hasPLengthLeOne_of_pElements_subset hH h

end

end CFSG.FeitThompson
