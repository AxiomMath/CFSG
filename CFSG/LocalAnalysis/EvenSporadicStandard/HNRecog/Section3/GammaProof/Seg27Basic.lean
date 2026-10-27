module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Generic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem gamma_derivedOf_subgroupOf {L M : Subgroup G} (hLM : L ≤ M) :
    derivedOf (L.subgroupOf M) = (derivedOf L).subgroupOf M := by
  apply Subgroup.map_injective M.subtype_injective
  have hcomp : M.subtype.comp (L.subgroupOf M).subtype =
      L.subtype.comp (Subgroup.subgroupOfEquivOfLe hLM).toMonoidHom := by
    ext x
    rfl
  have hcomm : (_root_.commutator ↥(L.subgroupOf M)).map
      (Subgroup.subgroupOfEquivOfLe hLM).toMonoidHom = _root_.commutator ↥L := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (Subgroup.subgroupOfEquivOfLe hLM).surjective]
  simp only [derivedOf]
  have hle : (_root_.commutator ↥L).map L.subtype ≤ M :=
    (Subgroup.map_subtype_le (_root_.commutator ↥L)).trans hLM
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hcomm,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]

theorem gamma_commutator_eq (M : Subgroup G) :
    _root_.commutator ↥M = (derivedOf M).subgroupOf M :=
  (Subgroup.comap_map_eq_self_of_injective M.subtype_injective (_root_.commutator ↥M)).symm

theorem gamma_isShapeZ2TimesSym_subgroupOf {L M : Subgroup G} (hLM : L ≤ M) {n : ℕ}
    (h : IsShapeZ2TimesSym n ↥L) : IsShapeZ2TimesSym n ↥(L.subgroupOf M) :=
  ⟨(Subgroup.subgroupOfEquivOfLe hLM).trans h.some⟩

theorem gamma_isShapeA5_subgroupOf {L M : Subgroup G} (hLM : L ≤ M) (h : IsShapeA5 ↥L) :
    IsShapeA5 ↥(L.subgroupOf M) :=
  ⟨(Subgroup.subgroupOfEquivOfLe hLM).trans h.some⟩

@[expose] noncomputable def gammaCommEquiv (M : Subgroup G) :
    ↥(_root_.commutator ↥M) ≃* ↥(derivedOf M) :=
  Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective

theorem gamma_commEquiv_coe (M : Subgroup G) (x : ↥(_root_.commutator ↥M)) :
    ((gammaCommEquiv M x : ↥(derivedOf M)) : G) = ((x : ↥M) : G) :=
  Subgroup.coe_equivMapOfInjective_apply _ M.subtype M.subtype_injective x

theorem gamma_hasSixOrbit_subgroupOf {M D : Subgroup G}
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator ↥M))
    (h : HasSixOrbit (φ.trans (gammaCommEquiv M)) D) : HasSixOrbit φ (D.subgroupOf M) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  have hcoe : ∀ g : alternatingGroup (Fin 8),
      ((φ.trans (gammaCommEquiv M)) g : G) = ((φ g : ↥M) : G) :=
    fun g => gamma_commEquiv_coe M (φ g)
  have hmem : ∀ g : alternatingGroup (Fin 8),
      (φ g : ↥M) ∈ D.subgroupOf M ↔ ((φ.trans (gammaCommEquiv M)) g : G) ∈ D := by
    intro g
    rw [Subgroup.mem_subgroupOf, hcoe g]
  have hset : {j : Fin 8 | ∃ g : alternatingGroup (Fin 8),
        (φ g : ↥M) ∈ D.subgroupOf M ∧ (g : Equiv.Perm (Fin 8)) i = j} =
      {j : Fin 8 | ∃ g : alternatingGroup (Fin 8),
        ((φ.trans (gammaCommEquiv M)) g : G) ∈ D ∧ (g : Equiv.Perm (Fin 8)) i = j} := by
    ext j
    constructor
    · rintro ⟨g, hg, hgj⟩
      exact ⟨g, (hmem g).mp hg, hgj⟩
    · rintro ⟨g, hg, hgj⟩
      exact ⟨g, (hmem g).mpr hg, hgj⟩
  rw [hset]
  exact hi

theorem gamma_seg27_typeS5 {L M : Subgroup G} (hLM : L ≤ M) (hs : IsShapeZ2TimesSym 5 ↥L)
    (hd : derivedOf L = L ⊓ derivedOf M) (ha : IsShapeA5 ↥(derivedOf L))
    (ho : ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf M), HasSixOrbit φ (derivedOf L))
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator ↥M)) :
    IsShapeZ2TimesSym 5 ↥(L.subgroupOf M) ∧
      derivedOf (L.subgroupOf M) = L.subgroupOf M ⊓ _root_.commutator ↥M ∧
      IsShapeA5 ↥(derivedOf (L.subgroupOf M)) ∧ HasSixOrbit φ (derivedOf (L.subgroupOf M)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact gamma_isShapeZ2TimesSym_subgroupOf hLM hs
  · rw [gamma_derivedOf_subgroupOf hLM, hd, gamma_commutator_eq M]
    ext x
    simp [Subgroup.mem_subgroupOf]
  · rw [gamma_derivedOf_subgroupOf hLM]
    exact gamma_isShapeA5_subgroupOf ((Subgroup.map_subtype_le (_root_.commutator ↥L)).trans hLM) ha
  · rw [gamma_derivedOf_subgroupOf hLM]
    exact gamma_hasSixOrbit_subgroupOf φ (ho (φ.trans (gammaCommEquiv M)))

end CFSG.EvenSporadicStandard.HNRecog.Section3
