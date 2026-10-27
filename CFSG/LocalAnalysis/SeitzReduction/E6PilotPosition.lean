module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotPositionFacts
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutDNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplitLayer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearSchreier
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesLevi
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteB

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore)

section D

variable {K : Type} [Field K]

theorem isSolvable_outer_a5Levi [Finite K] [CharP K 2] : Group.IsSolvable (Outer (a5Levi K)) := by
  have := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.linear_higher_schreier (K := K)
    (n := 6) (by norm_num)).2
  exact solvable_of_equiv ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 6 K)).trans (a5LeviEquiv K))

variable {G : Type*} [Group G] {L : Subgroup G}

noncomputable def a5LeviMapEquiv (e : L ≃* adjointGroup .E6 K) :
    a5Levi K ≃* (((a5Levi K).map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
  ((a5Levi K).equivMapOfInjective _ e.symm.injective).trans
    (((a5Levi K).map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)

theorem isSolvable_outer_map_a5Levi [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E6 K) :
    Group.IsSolvable (Outer (((a5Levi K).map e.symm.toMonoidHom).map L.subtype : Subgroup G)) := by
  have := isSolvable_outer_a5Levi (K := K)
  exact solvable_of_equiv (a5LeviMapEquiv e)

theorem center_map_a5Levi_eq_bot [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E6 K) :
    center (((a5Levi K).map e.symm.toMonoidHom).map L.subtype : Subgroup G) = ⊥ := by
  rw [← center_map_equiv (a5LeviMapEquiv e), center_a5Levi_eq_bot, Subgroup.map_bot]

theorem a5Levi_le_centralizer_posJ :
    a5Levi K ≤ centralizer (posJ K : Set (adjointGroup .E6 K)) := fun _ hd =>
  mem_centralizer_iff.2 fun _ hy =>
    commute_of_mem_subgroupOf_highRootSL2_of_mem_subgroupOf_perpLevi (Or.inl rfl) hy hd

theorem map_a5Levi_le_centralizer (e : L ≃* adjointGroup .E6 K) {X : Subgroup G}
    (hXJ : X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype) :
    ((a5Levi K).map e.symm.toMonoidHom).map L.subtype ≤ centralizer (X : Set G) :=
  (F4Pilot.map_le_centralizer_map L.subtype
    (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom a5Levi_le_centralizer_posJ)).trans
    (centralizer_le hXJ)

end D

theorem not_normal_map_oddCore_neighbour_E6 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hz : ZLeviOTwo K) (hF56 : FactF56E6 K)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype)
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
  have hf1 : 1 ≤ f := by omega
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨3, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).1⟩⟩
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have hXL : X ≤ L := hXJ.trans (map_subtype_le _)
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htK.1
  subst hDe
  exact EPilot.not_normal_map_oddCore_of_inner hset hOut e ht hKt
    (exists_conj_ne_mem_sup_zpowers_E6 hset hf1 K hK e ht hKt)
    (forall_inner_E6 hset hf1 K hK e ht hKt)
    (e6Rep K) (fun _ hx => exists_conj_eq_e6Rep hx)
    (posRadical K) (posLevi K) perfectCore_centralizer_e6Rep_eq isPGroup_posRadical
    posLevi_le_normalizer_posRadical disjoint_posRadical_posLevi
    (forall_normal_isPGroup_posLevi hz) (posJ_le_posLevi hq) (fun κ => e6Rep_mem_a5Levi κ)
    hF56 hXodd hXJ htX (map_a5Levi_le_centralizer e hXJ) (isQuasisimple_open_map_a5Levi e)
    (center_map_a5Levi_eq_bot e) (isSolvable_outer_map_a5Levi e) hsyl

theorem not_normal_neighbour_E6_nonsplit {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hz : ZLeviOTwo K) (hF56 : FactF56E6 K)
    {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hXL : X ≤ L := by
    rw [hX]
    exact map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hXJ : X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono hAJ)
  have hXodd : Odd (Nat.card X) := by
    rw [hX, card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective,
      hA, hK]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  exact not_normal_map_oddCore_neighbour_E6 hset hf hK e ht hKt hz hF56 hXodd hXJ hDe
    (neighbour_standard_E6_nonsplit hset.standard htC ht hKt hf hK e hAJ hA hcyc hX htX hDe).2.1

theorem not_normal_neighbour_E6_of_le_highTorusLine {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hz : ZLeviOTwo K) (hF56 : FactF56E6 K) {c : Kˣ} (hc : 3 ≤ orderOf c)
    {A : Subgroup (adjointGroup .E6 K)}
    (hAT : A ≤ (EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K))
    (hcA : (⟨CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6
      (EPilot.highDiag .E6 c), rootDiagUnit_highDiag_mem_adjointGroup (Or.inl rfl) c⟩ :
        adjointGroup .E6 K) ∈ A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hf1 : 1 ≤ f := by omega
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hXL : X ≤ L := by
    rw [hX]
    exact map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hTJ : (EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K) ≤ posJ K :=
    fun _ hx => mem_subgroupOf.2
      (EPilot.highTorusLine_le_highRootSL2 (Or.inl rfl) (mem_subgroupOf.1 hx))
  have hXJ : X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono (hAT.trans hTJ))
  have hTodd : Odd (Nat.card ((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (highTorusLine_le_adjointGroup (Or.inl rfl))).toEquiv]
    exact odd_card_highTorusLine hf1 hK
  have hXodd : Odd (Nat.card X) := by
    rw [hX, card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective]
    exact Odd.of_dvd_nat hTodd (card_dvd_of_le hAT)
  exact not_normal_map_oddCore_neighbour_E6 hset hf hK e ht hKt hz hF56 hXodd hXJ hDe
    (neighbour_standard_E6_of_centralizer_eq_sup hset.standard htC ht hKt hf hK e
      (centralizer_eq_highTorusLine_sup_of_le (Or.inl rfl) hc hAT hcA)
      highTorusLine_subgroupOf_le_centralizer_perpLevi highTorusLine_subgroupOf_le_centralizer_self
      hTodd hX htX hDe).2.1

end CFSG.SeitzReduction.E6Pilot
