module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleSplit
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.CyclicCase

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

structure Setting (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G)
    (J : Subgroup (EscapingQuotient z)) : Prop where
  square : SquareCaseSetting G S H z
  component : CFSG.IsComponent J
  not_le : ¬ J ≤ escapingImage H z
  rank : ∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z
  cyclic : TwoPointCyclic H z J

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)} (hs : Setting G S H z J)
include hs

theorem quotientData : EscapingQuotientData H z :=
  escapingQuotientData hs.square.core (hs.square.core.sylow_le hs.square.central.1)
    hs.square.central.2.1 hs.square.escape

theorem bar_mem : escapingBar z ∈ J :=
  hs.square.caseTwo J hs.component

theorem center_isPGroup : IsPGroup 2 (Subgroup.center J) :=
  (component_center_le_twoCore hs.quotientData.oddCore_eq_bot hs.component).1

theorem eq_bar_of_mem_center {c : J} (hc : c ∈ Subgroup.center J) (h2 : orderOf c = 2) :
    (c : EscapingQuotient z) = escapingBar z := by
  have hq := hs.quotientData
  exact eq_of_mem_twoCore_of_rank_one hq.bar_mem_center hq.bar_order hq.bar_mem_twoCore
    hq.twoCore_rank ((component_center_le_twoCore hq.oddCore_eq_bot hs.component).2
      (Subgroup.mem_map_of_mem _ hc)) (by rwa [Subgroup.orderOf_coe])

theorem bar_mem_center : (⟨escapingBar z, hs.bar_mem⟩ : J) ∈ Subgroup.center J :=
  Subgroup.mem_center_iff.mpr fun g => Subtype.ext
    (Subgroup.mem_center_iff.mp hs.quotientData.bar_mem_center g)

theorem center_ne_bot : Subgroup.center J ≠ ⊥ := by
  intro hbot
  have h := hs.bar_mem_center
  rw [hbot, Subgroup.mem_bot] at h
  have h2 := hs.quotientData.bar_order
  rw [show escapingBar z = 1 from congrArg Subtype.val h, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem center_isCyclic : IsCyclic (Subgroup.center J) := by
  refine CFSG.ABGLocalTools.isCyclic_of_isPGroup_two_of_comm hs.center_isPGroup
    (fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)) fun u v hu hv =>
      Subtype.ext (Subtype.ext ?_)
  have hu' : orderOf (u : J) = 2 := by rwa [Subgroup.orderOf_coe]
  have hv' : orderOf (v : J) = 2 := by rwa [Subgroup.orderOf_coe]
  rw [hs.eq_bar_of_mem_center u.2 hu', hs.eq_bar_of_mem_center v.2 hv']

theorem even_card_quotient : Even (Nat.card (J ⧸ Subgroup.center J)) := by
  obtain ⟨x, hxJ, hx2, hxz⟩ := hs.rank
  have hx2' : orderOf (⟨x, hxJ⟩ : J) = 2 := by rwa [Subgroup.orderOf_mk]
  have hxZ : (⟨x, hxJ⟩ : J) ∉ Subgroup.center J := fun h =>
    hxz (hs.eq_bar_of_mem_center h hx2')
  have hsq : (⟨x, hxJ⟩ : J) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (⟨x, hxJ⟩ : J)
    rwa [hx2'] at h
  have hord : orderOf (QuotientGroup.mk' (Subgroup.center J) ⟨x, hxJ⟩) = 2 := by
    refine orderOf_eq_prime ?_ fun h => hxZ ?_
    · rw [← map_pow, hsq, map_one]
    · rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk' (Subgroup.center J) ⟨x, hxJ⟩)
  rw [hord] at hdvd
  exact even_iff_two_dvd.mpr hdvd

theorem centralizer_ne_top : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
  intro htop
  have : IsSimpleGroup G := hs.square.core.simple
  have hzc : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
  rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.mem_bot] at hzc
    have h2 := hs.square.central.2.1
    rw [hzc, orderOf_one] at h2
    exact absurd h2 (by decide)
  · obtain ⟨a, b, hab⟩ := hs.square.core.nonabelian
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem card_quotient_lt : Nat.card (J ⧸ Subgroup.center J) < Nat.card G := by
  calc Nat.card (J ⧸ Subgroup.center J) ≤ Nat.card J :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    _ ≤ Nat.card (EscapingQuotient z) := Subgroup.card_le_card_group J
    _ ≤ Nat.card (Subgroup.centralizer ({z} : Set G)) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    _ < Nat.card G :=
        (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hs.centralizer_ne_top)).trans_eq
          Subgroup.card_top

theorem exists_sylow_le :
    ∃ Q : Sylow 2 J, (Q : Subgroup J) ≤ (escapingImage H z).subgroupOf J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hUH, -⟩ := hs.quotientData.sylow
  obtain ⟨Q, hQ⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal U hs.component.2
  refine ⟨Q, fun q hq => Subgroup.mem_subgroupOf.mpr ?_⟩
  have h : (q : EscapingQuotient z) ∈ (Q : Subgroup J).map J.subtype :=
    Subgroup.mem_map_of_mem _ hq
  rw [hQ] at h
  exact hUH h.1

theorem subgroupOf_ne_top : (escapingImage H z).subgroupOf J ≠ ⊤ := fun h =>
  hs.not_le fun x hx => by
    have hx' : (⟨x, hx⟩ : J) ∈ (escapingImage H z).subgroupOf J := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hx'

theorem isCyclic_of_twoPoint (g : J) (hg : g ∉ (escapingImage H z).subgroupOf J)
    (P : Subgroup J) (hP : IsPGroup 2 P)
    (hPB : ∀ p ∈ P, p ∈ (escapingImage H z).subgroupOf J ∧
      g⁻¹ * p * g ∈ (escapingImage H z).subgroupOf J) : IsCyclic P := by
  have h := hs.cyclic g g.2 (fun h => hg (Subgroup.mem_subgroupOf.mpr h)) (P.map J.subtype)
    (hP.map J.subtype) fun p hp => by
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
      obtain ⟨h1, h2⟩ := hPB q hq
      exact ⟨q.2, Subgroup.mem_subgroupOf.mp h1, Subgroup.mem_subgroupOf.mp h2⟩
  exact isCyclic_of_surjective (P.equivMapOfInjective J.subtype J.subtype_injective).symm
    (MulEquiv.surjective _)

end Setting

end CFSG.ProperTwoGeneratedCore.Lemma37.CyclicCase
