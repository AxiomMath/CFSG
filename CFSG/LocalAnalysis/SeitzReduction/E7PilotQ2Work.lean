module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2HR8
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2BLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.SeitzReduction.OmegaPilot (NeighbourOvergroupOmega OmegaCatalogueClausesAt)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {t : G}

theorem E7Work.neighbour_standard_nonsplit_two (h : E7Work L K t 1)
    (e : L ≃* adjointGroup .E7 K) {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K)
    (hA : Nat.card A = 3) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
  neighbour_standard_E7_nonsplit_two h.standard.standard h.mem_centralizer h.orderOf_eq
    (h.inf_eq e) (by simpa using h.card_eq) e hAJ hA hX htX hDe

theorem E7Work.neighbour_overgroup_nonsplit_two (hcat : OmegaCatalogueClausesAt 6)
    (h : E7Work L K t 1) (e : L ≃* adjointGroup .E7 K) {A : Subgroup (adjointGroup .E7 K)}
    (hAJ : A ≤ posJE7 K) (hA : Nat.card A = 3) {X : Subgroup G}
    (hX : X = (A.map e.symm.toMonoidHom).map L.subtype) (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 1 :=
  (neighbour_overgroup_E7_nonsplit_two hcat h.standard (by simpa using h.card_eq) e h.orderOf_eq
    (h.inf_eq e) hAJ hA hX htX hDe).1

theorem isPGroup_outer_of_mulEquiv_E7_two (hK : Nat.card K = 2) (e : L ≃* adjointGroup .E7 K) :
    IsPGroup 2 (Outer L) := by
  intro g
  refine ⟨0, ?_⟩
  induction g using QuotientGroup.induction_on with
  | H α =>
    rw [pow_zero, pow_one, ← QuotientGroup.mk_one, QuotientGroup.eq]
    exact forall_mem_range_conj_of_mulEquiv_E7_two hK e _

theorem inf_centralizer_inf_centralizer_le_nonsplit_E7 [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .E7 K) {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K)
    (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A) :
    L ⊓ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) ⊓
        centralizer ((((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype :
          Subgroup G) : Set G) ≤ (A.map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨-, -, hAD⟩ := centralizer_nonsplit_E7_of_finite hAJ hA hcyc
  exact SeitzQ2.inf_centralizer_le_of_le_sup
    (inf_centralizer_nonsplit_E7_of_finite e hAJ hA hcyc).le
    (F4Pilot.map_le_centralizer_map L.subtype
      (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom hAD))
    (center_map_map_perpLevi_E7_eq_bot e)

theorem not_mem_of_mem_centralizer_E7 [Finite K] (e : L ≃* adjointGroup .E7 K)
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) : t ∉ L := by
  intro htL
  have hZ : center L = ⊥ := by
    rw [← map_center_eq e.symm, center_adjointGroup_eq_bot, Subgroup.map_bot]
  have hmem : (⟨t, htL⟩ : L) ∈ center L :=
    mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 htC y y.2)
  rw [hZ, mem_bot] at hmem
  have h1 : t = 1 := congrArg Subtype.val hmem
  rw [h1, orderOf_one] at ht
  exact absurd ht (by decide)

end CFSG.SeitzReduction.E7Pilot
