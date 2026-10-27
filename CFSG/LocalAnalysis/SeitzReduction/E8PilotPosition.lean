module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionOuter
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionB

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms

section D

variable {K : Type} [Field K]

variable {G : Type*} [Group G] {L : Subgroup G}

noncomputable def e7LeviMapEquivE8 (e : L ≃* adjointGroup .E8 K) :
    e7Levi K ≃* (((e7Levi K).map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
  ((e7Levi K).equivMapOfInjective _ e.symm.injective).trans
    (((e7Levi K).map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)

theorem e7Levi_le_centralizer_posJE8 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    e7Levi K ≤ centralizer (posJE8 K : Set (adjointGroup .E8 K)) :=
  (EPilot.centralizer_highRootSL2_subgroupOf (Or.inr (Or.inr rfl)) hq).symm.le

theorem map_e7Levi_le_centralizer [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (e : L ≃* adjointGroup .E8 K) {X : Subgroup G}
    (hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype) :
    ((e7Levi K).map e.symm.toMonoidHom).map L.subtype ≤ centralizer (X : Set G) :=
  (F4Pilot.map_le_centralizer_map L.subtype
    (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom (e7Levi_le_centralizer_posJE8 hq))).trans
    (centralizer_le hXJ)

end D

theorem not_normal_map_oddCore_neighbour_E8 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF5 : FactF5E8 K)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_E8 e
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hXL : X ≤ L := hXJ.trans (map_subtype_le _)
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  obtain ⟨g, z, hzL, hgz, hz1, hzU⟩ :=
    exists_conj_eq_mul_twoCentral_E8_of_two_le hset hf hK e ht hKt
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_le_centralizer_mulEquiv_of_conj_eq_mul_E8 hset hOut hq e
    (factF56E8_of_factF5E8 hq hF5) htC ht hXodd hXJ hzL hz1 hzU hgz
  subst hDe
  set eD := e7LeviMapEquivE8 (G := G) e with heD
  have hDL : ((e7Levi K).map e.symm.toMonoidHom).map L.subtype ≤ L := map_subtype_le _
  have hyD : (e.symm (repXE8 K) : G) ∈ ((e7Levi K).map e.symm.toMonoidHom).map L.subtype :=
    ⟨e.symm (repXE8 K), ⟨repXE8 K, repXE8_mem_e7Levi, rfl⟩, rfl⟩
  have hy1 : (e.symm (repXE8 K) : G) ≠ 1 := by
    intro h
    apply repXE8_ne_one (K := K)
    have h' : e.symm (repXE8 K) = 1 := Subtype.ext h
    rw [← e.apply_symm_apply (repXE8 K), h', map_one]
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht
    (map_e7Levi_le_centralizer hq e hXJ)
    (F4Pilot.isQuasisimple_open_of_mulEquiv eD isQuasisimple_open_e7Levi)
    (F4Pilot.center_eq_bot_congr eD center_e7Levi_eq_bot)
    ⟨⟨2, derivedSeries_outer_eq_bot_of_mulEquiv (eD.symm.trans (e7LeviEquiv K))
      (exceptional_E_pinned_model_Schreier K).2.1⟩⟩
    (hDL.trans hLt) hsyl hyD hy1 (Or.inr rfl) hP ⟨eP.trans eD⟩

end CFSG.SeitzReduction.E8Pilot
