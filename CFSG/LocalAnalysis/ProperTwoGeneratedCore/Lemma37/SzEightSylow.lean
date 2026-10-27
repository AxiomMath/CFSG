module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightEmbed
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC

theorem mul_self_eq_one_of_torus {K : Type*} [Group K]
    (hZ : ∀ c ∈ Subgroup.center K, c * c = 1) {Q : Subgroup K}
    (hB : BenderBorelFacts (K ⧸ Subgroup.center K) (Q.map (QuotientGroup.mk' (Subgroup.center K))))
    {x : K} (hx : x * x = 1)
    (hxc : InCenterOf (Q.map (QuotientGroup.mk' (Subgroup.center K))) (x : K ⧸ Subgroup.center K))
    (hx1 : (x : K ⧸ Subgroup.center K) ≠ 1) {w : K}
    (hwc : InCenterOf (Q.map (QuotientGroup.mk' (Subgroup.center K))) (w : K ⧸ Subgroup.center K)) :
    w * w = 1 := by
  by_cases hw1 : (w : K ⧸ Subgroup.center K) = 1
  · exact hZ w ((QuotientGroup.eq_one_iff w).mp hw1)
  obtain ⟨D, -, -, -, htrans, -⟩ := hB.torus
  obtain ⟨d, -, hd⟩ := htrans _ _ hxc hx1 hwc hw1
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective d
  have hc : (e⁻¹ * x * e)⁻¹ * w ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq]
    rw [← hd, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  set c := (e⁻¹ * x * e)⁻¹ * w with hcdef
  have hw : w = e⁻¹ * x * e * c := by rw [hcdef]; group
  have hcc := Subgroup.mem_center_iff.mp hc
  rw [hw]
  calc e⁻¹ * x * e * c * (e⁻¹ * x * e * c) = e⁻¹ * (x * x) * e * (c * c) := by
        rw [mul_assoc (e⁻¹ * x * e) c, ← mul_assoc c, ← hcc (e⁻¹ * x * e)]
        group
    _ = 1 := by rw [hx, hZ c hc]; group

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G}

noncomputable def sylowJ (hz : IsCentralInvolution (S : Subgroup G) z)
    (J : Subgroup (EscapingQuotient z)) [J.Normal] : Sylow 2 J :=
  CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal (sylowBarSylow hz) J

theorem mem_sylowJ_iff (hz : IsCentralInvolution (S : Subgroup G) z)
    {J : Subgroup (EscapingQuotient z)} [J.Normal] (v : J) :
    v ∈ (sylowJ hz J : Subgroup J) ↔ (v : EscapingQuotient z) ∈ escapingSylowImage S z := by
  rw [sylowJ, CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe, Subgroup.mem_comap,
    coe_sylowBarSylow, sylowBar_range]
  rfl

noncomputable def sylowStar (hz : IsCentralInvolution (S : Subgroup G) z)
    (J : Subgroup (EscapingQuotient z)) [J.Normal] : Sylow 2 (J ⧸ Subgroup.center J) :=
  (sylowJ hz J).mapSurjective (QuotientGroup.mk'_surjective _)

theorem coe_sylowStar (hz : IsCentralInvolution (S : Subgroup G) z)
    (J : Subgroup (EscapingQuotient z)) [J.Normal] :
    (sylowStar hz J : Subgroup (J ⧸ Subgroup.center J)) =
      (sylowJ hz J : Subgroup J).map (QuotientGroup.mk' _) :=
  Sylow.coe_mapSurjective _ _

theorem exists_mk_eq_of_mem_sylowStar (hz : IsCentralInvolution (S : Subgroup G) z)
    {J : Subgroup (EscapingQuotient z)} [J.Normal] {r : J ⧸ Subgroup.center J}
    (hr : r ∈ (sylowStar hz J : Subgroup (J ⧸ Subgroup.center J))) :
    ∃ v : J, (v : EscapingQuotient z) ∈ escapingSylowImage S z ∧
      (v : J ⧸ Subgroup.center J) = r := by
  rw [coe_sylowStar] at hr
  obtain ⟨v, hv, rfl⟩ := hr
  exact ⟨v, (mem_sylowJ_iff hz v).mp hv, rfl⟩

namespace SzEightSetting

variable {H : Subgroup G} {J : Subgroup (EscapingQuotient z)} [J.Normal]
  (hs : SzEightSetting S H z J)
include hs

theorem center_le_sylowJ : Subgroup.center J ≤ (sylowJ hs.central J : Subgroup J) := by
  intro c hc
  rw [mem_sylowJ_iff]
  rcases hs.center c hc with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_map.mpr ⟨escapingSelf z, Subgroup.mem_subgroupOf.mpr hs.central.1, rfl⟩

theorem exists_involution_sylowJ : ∃ x : J, x ∈ (sylowJ hs.central J : Subgroup J) ∧
    x * x = 1 ∧ x ∉ Subgroup.center J := by
  obtain ⟨x, hxJ, hx, hxne, hxS⟩ := hs.exists_involution_mem_sylow
  refine ⟨⟨x, hxJ⟩, (mem_sylowJ_iff hs.central _).mpr hxS, Subtype.ext ?_, ?_⟩
  · change x * x = 1
    rw [← pow_two]
    have h2 := pow_orderOf_eq_one x
    rwa [hx] at h2
  · rw [hs.mem_center_iff]
    rintro (h | h)
    · rw [show x = 1 from h, orderOf_one] at hx
      exact absurd hx (by decide)
    · exact hxne h

theorem borelFacts
    : BenderBorelFacts (J ⧸ Subgroup.center J)
    ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _)) := by
  rw [← coe_sylowStar]
  exact benderBorelFactsHold _ hs.isBenderGroup _

theorem mul_self_eq_one_of_inCenterOf
    {x : J} (hxx : x * x = 1) (hxZ : x ∉ Subgroup.center J)
    (hxc : InCenterOf ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _))
      (x : J ⧸ Subgroup.center J))
    {w : J} (hwc : InCenterOf ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _))
      (w : J ⧸ Subgroup.center J)) : w * w = 1 :=
  mul_self_eq_one_of_torus (fun _ hc => hs.mul_self_of_mem_center hc) hs.borelFacts hxx hxc
    (fun h => hxZ ((QuotientGroup.eq_one_iff x).mp h)) hwc

end SzEightSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
