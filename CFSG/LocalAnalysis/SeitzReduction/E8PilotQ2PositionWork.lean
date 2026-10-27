module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionHR8
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainSetup

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {t : G}

theorem E8Work.not_normal_neighbour_nonsplit_two (h : E8Work L K t 1)
    (e : L ≃* adjointGroup .E8 K) {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K)
    (hA : Nat.card A = Nat.card K + 1) {X : Subgroup G}
    (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_neighbour_E8_nonsplit_two h.standard (by simpa using h.card_eq) e h.orderOf_eq
    (h.inf_eq e) hAJ hA hX hDe

theorem E8Work.exists_not_normal_neighbour_nonsplit_two (h : E8Work L K t 1)
    (e : L ≃* adjointGroup .E8 K) :
    ∃ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K ∧ IsCyclic A ∧
      Nat.card A = Nat.card K + 1 ∧
      t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) ∧
      ¬ (((((e7Levi K).map e.symm.toMonoidHom).map L.subtype).subgroupOf
          (centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G))))).Normal := by
  have := F4Pilot.finite_of_natCard_eq_two_pow h.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow h.card_eq
  obtain ⟨A, hAJ, hcyc, hA⟩ := exists_nonsplit_le_posJE8 (K := K)
  refine ⟨A, hAJ, hcyc, hA, centralizer_le (map_subtype_le _) h.mem_centralizer,
    h.not_normal_neighbour_nonsplit_two e hAJ hA rfl rfl⟩

theorem E8Work.neighbour_overgroup_nonsplit_two (hcat : E7CatalogueClauses) (h : E8Work L K t 1)
    (e : L ≃* adjointGroup .E8 K) {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K)
    (hA : Nat.card A = Nat.card K + 1) {X : Subgroup G}
    (hX : X = (A.map e.symm.toMonoidHom).map L.subtype) (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupE7 (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 1 :=
  neighbour_overgroup_E8_nonsplit_two hcat h.standard (by simpa using h.card_eq) e h.orderOf_eq
    (h.inf_eq e) hAJ hA hX htX hDe

end CFSG.SeitzReduction.E8Pilot
