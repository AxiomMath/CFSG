module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightDecomp

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC

variable {G : Type} [Group G] [Finite G]

structure SzEightExclSetting (S : Sylow 2 G) (H : Subgroup G) (z : G)
    (J : Subgroup (EscapingQuotient z)) : Prop where
  square : SquareCaseSetting G S H z
  component : CFSG.IsComponent J
  involution : ∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z
  center : ∀ c ∈ Subgroup.center J, (c : EscapingQuotient z) = 1 ∨
    (c : EscapingQuotient z) = escapingBar z

namespace SzEightExclSetting

variable {S : Sylow 2 G} {H : Subgroup G} {z : G} {J : Subgroup (EscapingQuotient z)}
  (hs : SzEightExclSetting S H z J)
include hs

theorem central : IsCentralInvolution (S : Subgroup G) z := hs.square.central

theorem quotientData : EscapingQuotientData H z :=
  escapingQuotientData hs.square.core (hs.square.core.sylow_le hs.square.central.1)
    hs.square.central.2.1 hs.square.escape

theorem bar_mem : escapingBar z ∈ J := hs.square.caseTwo J hs.component

theorem normal : J.Normal := by
  obtain ⟨x, hxJ, hx, hne⟩ := hs.involution
  exact hs.quotientData.component_normal_of_two_le_pRank hs.component
    (two_le_pRank_of_commuting_involutions hxJ hs.bar_mem hx hs.quotientData.bar_order hne
      (hs.quotientData.commute_bar x))

theorem mem_center_iff (c : J) :
    c ∈ Subgroup.center J ↔ (c : EscapingQuotient z) = 1 ∨ (c : EscapingQuotient z) = escapingBar z
    := by
  refine ⟨hs.center c, ?_⟩
  rintro (h | h)
  · rw [show c = 1 from Subtype.ext h]
    exact Subgroup.one_mem _
  · exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h]
      exact (hs.quotientData.commute_bar g).eq)

theorem mul_self_of_mem_center {c : J} (hc : c ∈ Subgroup.center J) : c * c = 1 := by
  apply Subtype.ext
  rcases hs.center c hc with h | h
  · rw [Subgroup.coe_mul, h, one_mul, Subgroup.coe_one]
  · rw [Subgroup.coe_mul, h, Subgroup.coe_one, ← pow_two]
    have h2 := pow_orderOf_eq_one (escapingBar z)
    rwa [hs.quotientData.bar_order] at h2

theorem center_quotient_eq_bot : Subgroup.center (J ⧸ Subgroup.center J) = ⊥ := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hs.component.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (J ⧸ Subgroup.center J)) with
    h | h
  · exact h
  · exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)) hab

variable [J.Normal]

theorem exists_involution_sylowJ : ∃ x : J, x ∈ (sylowJ hs.central J : Subgroup J) ∧
    x * x = 1 ∧ x ∉ Subgroup.center J := by
  obtain ⟨x, hxJ, hx, hne⟩ := hs.involution
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_of_pow (sylowBarSylow hs.central) (n := 1)
    (x := x) (by rw [pow_one]; have h := pow_orderOf_eq_one x; rwa [hx] at h)
  rw [coe_sylowBarSylow, sylowBar_range] at hg
  have hx' : orderOf (g * x * g⁻¹) = 2 := by
    simpa only [MulAut.conj_apply] using ((MulAut.conj g).orderOf_eq x).trans hx
  refine ⟨⟨g * x * g⁻¹, Subgroup.Normal.conj_mem inferInstance x hxJ g⟩,
    (mem_sylowJ_iff hs.central _).mpr hg, Subtype.ext ?_, ?_⟩
  · change g * x * g⁻¹ * (g * x * g⁻¹) = 1
    rw [← pow_two]
    have h2 := pow_orderOf_eq_one (g * x * g⁻¹)
    rwa [hx'] at h2
  · rw [hs.mem_center_iff]
    rintro (h | h)
    · change g * x * g⁻¹ = 1 at h
      rw [h, orderOf_one] at hx'
      exact absurd hx' (by decide)
    · change g * x * g⁻¹ = escapingBar z at h
      apply hne
      rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group, h, (hs.quotientData.commute_bar g⁻¹).eq,
        mul_assoc, inv_mul_cancel, mul_one]

variable (e : (J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1))
include e

theorem borelFacts : BenderBorelFacts (J ⧸ Subgroup.center J)
    ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _)) := by
  rw [← coe_sylowStar]
  exact benderBorelFactsHold _ (.isSuzuki 1 le_rfl e) _

theorem sylowFacts :
    SzEightSylowFacts (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J)) :=
  szEightSylowFacts_of_mulEquiv e _

theorem exists_isInnerPart :
    ∃ φ : (S : Subgroup G) →* J ⧸ Subgroup.center J,
    IsInnerPart hs.central φ := by
  have hmem : ∀ s : (S : Subgroup G), sylowBar hs.central s ∈ escapingSylowImage S z :=
    fun s => by
      rw [← sylowBar_range hs.central]
      exact ⟨s, rfl⟩
  have hP : IsPGroup 2 (escapingSylowImage S z) := by
    have h := (sylowBarSylow hs.central).isPGroup'
    rwa [coe_sylowBarSylow, sylowBar_range] at h
  set P := escapingSylowImage S z
  set ψ := innerPart (SzEightSetting.odd_card_outer e) hs.center_quotient_eq_bot P hP
  let ι : (S : Subgroup G) →* P := (sylowBar hs.central).codRestrict P hmem
  have hψJ : ∀ (w : P) (h : (w : EscapingQuotient z) ∈ J), ψ w = ((⟨w, h⟩ : J) : J ⧸ _) :=
    fun w h => innerPart_eq_mk _ _ _ _ w h
  have hQ : (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J)) ≤ ψ.range := by
    intro r hr
    obtain ⟨v, hvS, rfl⟩ := exists_mk_eq_of_mem_sylowStar hs.central hr
    exact ⟨⟨v, hvS⟩, hψJ ⟨v, hvS⟩ v.2⟩
  refine ⟨ψ.comp ι, fun s => innerPart_mem_sylow _ _ _ _ _ hQ (ι s), fun s h => hψJ (ι s) h,
    fun s h => mem_centralizer_of_innerPart_eq_one (SzEightSetting.odd_card_outer e)
      hs.center_quotient_eq_bot P hP hs.component.1.1.commutator_eq_top (ι s) h⟩

theorem inCenterOf_of_sq_eq_one {r : J ⧸ Subgroup.center J}
    (hr : r ∈ (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J))) (hrr : r * r = 1) :
    InCenterOf ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _)) r := by
  rw [← coe_sylowStar]
  refine ⟨hr, fun q hq => ?_⟩
  have h := (hs.sylowFacts e).comm_of_sq ⟨r, hr⟩ (Subtype.ext (by
    rw [Subgroup.coe_pow, pow_two]; exact hrr)) ⟨q, hq⟩
  exact (congrArg Subtype.val h).symm

theorem mul_self_ne_bar
    {q : J} (hq : q ∈ (sylowJ hs.central J : Subgroup J)) :
    (q * q : J) ≠ ⟨escapingBar z, hs.bar_mem⟩ := by
  intro h
  have hmk : ∀ {v : J}, v ∈ (sylowJ hs.central J : Subgroup J) →
      (v : J ⧸ Subgroup.center J) ∈ (sylowStar hs.central J : Subgroup _) := fun hv => by
    rw [coe_sylowStar]
    exact ⟨_, hv, rfl⟩
  obtain ⟨x, hxQ, hxx, hxZ⟩ := hs.exists_involution_sylowJ
  have hxc := hs.inCenterOf_of_sq_eq_one e (hmk hxQ) (by
    rw [← QuotientGroup.mk_mul, hxx, QuotientGroup.mk_one])
  have hqq : ((q : J ⧸ Subgroup.center J)) * q = 1 := by
    rw [← QuotientGroup.mk_mul, h, QuotientGroup.eq_one_iff, hs.mem_center_iff]
    exact Or.inr rfl
  have h1 := mul_self_eq_one_of_torus (fun _ hc => hs.mul_self_of_mem_center hc)
    (hs.borelFacts e) hxx hxc (fun h' => hxZ ((QuotientGroup.eq_one_iff x).mp h'))
    (hs.inCenterOf_of_sq_eq_one e (hmk hq) hqq)
  rw [h1] at h
  have h2 := congrArg Subtype.val h
  have h3 := hs.quotientData.bar_order
  rw [← show (1 : EscapingQuotient z) = escapingBar z from h2, orderOf_one] at h3
  exact absurd h3 (by decide)

end SzEightExclSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
