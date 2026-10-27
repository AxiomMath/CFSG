module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionC
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionAut
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassRepsCenter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassRepsPerfect
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUPerfect
public import CFSG.LieType.Chevalley.DiagramFixedModelSchreier
public import CFSG.LieType.Chevalley.ExceptionalSmallRankSchreier

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_normal_map_oddCore_neighbour {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hC1 : OuterFusionTwoCentral L t)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (((rootSL2R K).subgroupOf (adjointGroup .F4 K)).map e.symm.toMonoidHom).map
      L.subtype)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have hf1 : 1 ≤ f := by omega
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨5, derivedSeries_outer_eq_bot_of_mulEquiv e
      ((exceptional_ordinary_small_rank_Schreier .F4 K).2 (Or.inl rfl))⟩⟩
  exact not_normal_map_oddCore_of_facts hset hOut hq e center_adjointGroup_eq_bot
    (isSolvable_outer_C3Levi hK) factF1 factF2 factF3 (factF3Perfect hq) (factLeviSimple K hq)
    (factF4b hq) (factF5 K) (factF6 hq) (factF7 hf1 hK) ht hKt hC1 hXodd hXJ hDe hsyl

theorem not_normal_map_oddCore_torusLineR {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hC1 : OuterFusionTwoCentral L t)
    {X : Subgroup G} (hX : X = (((torusLineR K).subgroupOf (adjointGroup .F4 K)).map
      e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hXL : X ≤ L := by
    rw [hX]
    exact map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hTJ : (torusLineR K).subgroupOf (adjointGroup .F4 K) ≤
      (rootSL2R K).subgroupOf (adjointGroup .F4 K) := by
    intro x hx
    obtain ⟨c, hc⟩ := mem_torusLineR.1 (mem_subgroupOf.1 hx)
    rw [mem_subgroupOf, ← hc]
    exact rootDiagUnit_rDiag_mem_rootSL2R c
  have hXJ : X ≤ (((rootSL2R K).subgroupOf (adjointGroup .F4 K)).map e.symm.toMonoidHom).map
      L.subtype := by
    rw [hX]
    exact map_mono (map_mono hTJ)
  have hXodd : Odd (Nat.card X) := by
    rw [hX, card_map_of_injective L.subtype_injective,
      card_map_of_injective e.symm.injective,
      Nat.card_congr (subgroupOfEquivOfLe torusLineR_le_adjointGroup).toEquiv]
    exact odd_card_torusLineR (one_le_of_natCard_eq_two_pow hK) hK
  exact not_normal_map_oddCore_neighbour hset hf hK e ht hKt hC1 hXodd hXJ hDe
    (neighbour_standard_torusLineR hset.standard htC ht hKt hf hK e hX htX hDe).2.1

end CFSG.SeitzReduction.F4Pilot
