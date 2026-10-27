module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FusionZStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FusionTwoConstrained
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FusionSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FusionW3Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FusionW3Card
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ReifartTransport

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
  CFSG.Monster.GMS

theorem IsTwoBCover.of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : IsTwoBCover L) : IsTwoBCover L' := by
  obtain ⟨hp, hc, ⟨f⟩⟩ := h
  refine ⟨Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective, ?_, ?_⟩
  · have h1 : Nat.card (center L') = Nat.card (center L) := by
      rw [← Subgroup.map_center_eq e]
      exact (Nat.card_congr
        ((center L).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
    rw [h1]
    exact hc
  · exact ⟨(QuotientGroup.congr (center L') (center L) e.symm
      (Subgroup.map_center_eq e.symm)).trans f⟩

section Transport

variable {G : Type} [Group G]

theorem natCard_centralizer_subgroup (X : Subgroup G) {w : G} (hw : w ∈ X) :
    Nat.card ↥(centralizer ({(⟨w, hw⟩ : ↥X)} : Set ↥X)) =
      Nat.card ↥(X ⊓ centralizer ({w} : Set G)) :=
  Nat.card_congr (centralizerEquivInf' hw).toEquiv

theorem isTwoConstrained_centralizer_subgroup (X : Subgroup G) {w : G} (hw : w ∈ X)
    (h : IsTwoConstrained (X ⊓ centralizer ({w} : Set G))) :
    IsTwoConstrained (centralizer ({(⟨w, hw⟩ : ↥X)} : Set ↥X)) :=
  DS81.Reifart.centralizer_O2In_le (centralizerEquivInf' hw) h

end Transport

@[expose] def TwoBLocalFourW3 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsTwoBCover L → ∀ t : L, t ∈ center L → orderOf t = 2 →
    ∀ w : L, orderOf w = 2 → w ∉ center L →
      (Nat.card ↥(centralizer ({w} : Set L)) = babyCentOrder 2 ∨
        Nat.card ↥(centralizer ({w} : Set L)) = 2 * babyCentOrder 2) →
      IsTwoConstrained (centralizer ({w} : Set L)) →
      (center ↥(centralizer ({w} : Set L))).map (centralizer ({w} : Set L)).subtype =
        zpowers w ⊔ zpowers t

theorem false_of_center_eq {X : Type} [Group X] [Finite X] {tt : X} (htt2 : orderOf tt = 2)
    (htt : tt ∈ center X) {w : X} (hw : orderOf w = 2)
    (hc : (center ↥(centralizer ({w} : Set X))).map (centralizer ({w} : Set X)).subtype =
      zpowers w ⊔ zpowers tt) {s : X} (hs : s ∈ centralizer ({w} : Set X))
    (hsc : ∀ y ∈ centralizer ({w} : Set X), y * s = s * y)
    (hs1 : s ≠ 1) (hsw : s ≠ w) (hst : s ≠ tt) (hswt : s ≠ w * tt) : False := by
  have hmem : s ∈ (center ↥(centralizer ({w} : Set X))).map
      (centralizer ({w} : Set X)).subtype :=
    ⟨⟨s, hs⟩, mem_center_iff.2 fun y => Subtype.ext (hsc y y.2), rfl⟩
  rw [hc] at hmem
  have hwt : w * tt = tt * w := mem_center_iff.1 htt w
  rcases mem_pair_cases hw htt2 hwt hmem with h | h | h | h
  exacts [hs1 h, hsw h, hst h, hswt h]

section Certified


theorem ds81Lemma55Fusion_of_w3 (hT3 : BabyTableIII) (h3 : TwoBLocalFourW3) :
    DS81Lemma55Fusion := by
  intro G _ _ L t z h hc h54 hCt hle
  subst hCt
  have : IsSimpleGroup G := h.std.simple
  obtain ⟨d⟩ := h.exists_level55 hc rfl
  have hz2 : orderOf z = 2 := d.z_ord
  have ht2 : orderOf t = 2 := d.t_ord
  have hzt : z * t = t * z := d.zt_comm
  have hzne : z ≠ t := d.z_ne_t
  have hzL : z ∈ centralizer ({t} : Set G) := hc.hz
  have hL2 : (Nat.card ↥(centralizer ({t} : Set G))).factorization 2 =
      (Nat.card ↥(centZ z)).factorization 2 := by
    have h0 := hc.loc.twoCentral
    rw [natCard_centralizer_subgroup (centralizer ({t} : Set G)) hzL,
      inf_eq_right.2 hle] at h0
    exact h0.symm
  have hne : ¬ centralizer ({t} : Set G) ≤ centZ z := by
    intro hcz
    have hzc : (⟨z, hzL⟩ : ↥(centralizer ({t} : Set G))) ∈
        center ↥(centralizer ({t} : Set G)) := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (hcz y.2))
    have hz' : z ∈ (center ↥(centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype := ⟨_, hzc, rfl⟩
    rw [h.center_eq] at hz'
    rcases eq_one_or_eq_of_mem_zpowers_two ht2 hz' with h1 | h1
    · rw [h1, orderOf_one] at hz2
      exact absurd hz2 (by decide)
    · exact hzne h1
  have hlt : Nat.card ↥(centZ z) < Nat.card ↥(centralizer ({t} : Set G)) := by
    by_contra hge
    exact hne (eq_of_le_of_card_ge hle (not_lt.1 hge) ▸ le_rfl)
  obtain ⟨T, hTK, hTZ, hTw⟩ := exists_sylow_centZ d h54 hle hL2 hne
  have htpair : t ∈ pair z t := t_mem_pair z t
  have htT : t ∈ (T : Subgroup G) := ((hTZ t).1 htpair).1
  have htc : ∀ s ∈ (T : Subgroup G), s * t = t * s := fun s hs => ((hTZ t).1 htpair).2 s hs
  obtain ⟨g, hgT, hgt⟩ := exists_conj_mem_sylow_ne h.std.nonabelian T htT htc ht2
  have ht1pair : g⁻¹ * t * g ∉ pair z t := fun hp => hgt (hTw g hp)
  have ht1K : g⁻¹ * t * g ∈ centZ z := hTK hgT
  have ht1Lt : g⁻¹ * t * g ∈ centralizer ({t} : Set G) := hle ht1K
  have ht1ord : orderOf (g⁻¹ * t * g) = 2 := by
    rw [← ht2]
    exact (isConj_iff.2 ⟨g⁻¹, by simp⟩ : IsConj t (g⁻¹ * t * g)).orderOf_eq.symm
  generalize ht1def : g⁻¹ * t * g = t1 at ht1pair ht1K ht1Lt ht1ord hgt hgT
  have ht1z : t1 * z = z * t1 := mem_centralizer_singleton_iff.1 ht1K
  have ht1t : t1 * t = t * t1 := mem_centralizer_singleton_iff.1 ht1Lt
  set X : Subgroup G := centralizer ({t1} : Set G) with hXdef
  have hzX : z ∈ X := mem_centralizer_singleton_iff.2 ht1z.symm
  have htX : t ∈ X := mem_centralizer_singleton_iff.2 ht1t.symm
  have ht1X : t1 ∈ X := mem_centralizer_singleton_iff.2 rfl
  have eX : ↥(centralizer ({t} : Set G)) ≃* ↥X :=
    (centralizerEquiv (MulAut.conj g⁻¹) t).trans (MulEquiv.subgroupCongr (by
      rw [hXdef, ← ht1def]; simp))
  have hcovX : IsTwoBCover ↥X :=
    IsTwoBCover.of_mulEquiv eX (IsTwoBCover.of_stdHyp h.std h.card_center h.quot_B)
  have htt : (⟨t1, ht1X⟩ : ↥X) ∈ center ↥X := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.1 y.2)
  have htt2 : orderOf (⟨t1, ht1X⟩ : ↥X) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ht1ord
  have hw2 : orderOf (⟨z, hzX⟩ : ↥X) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hz2
  have hwc : (⟨z, hzX⟩ : ↥X) ∉ center ↥X := by
    intro hzc
    have hXK : X ≤ centZ z := fun x hx =>
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_center_iff.1 hzc ⟨x, hx⟩))
    have := Subgroup.card_le_of_le hXK
    rw [← Nat.card_congr eX.toEquiv] at this
    omega
  obtain ⟨k, hk⟩ := exists_card_centralizer_cases hT3 hcovX hw2 hwc
  rw [natCard_centralizer_subgroup X hzX, hXdef, inf_comm] at hk
  have hk2 : k = 2 := d.eq_two_of_card_cases hle ht1K ht1pair hk
  subst hk2
  have hcard : Nat.card ↥(centralizer ({(⟨z, hzX⟩ : ↥X)} : Set ↥X)) = babyCentOrder 2 ∨
      Nat.card ↥(centralizer ({(⟨z, hzX⟩ : ↥X)} : Set ↥X)) = 2 * babyCentOrder 2 := by
    rw [natCard_centralizer_subgroup X hzX, hXdef, inf_comm]
    exact hk
  have hcon : IsTwoConstrained (centralizer ({(⟨z, hzX⟩ : ↥X)} : Set ↥X)) :=
    isTwoConstrained_centralizer_subgroup X hzX (by
      rw [hXdef, inf_comm]
      exact IsTwoConstrained.inf_centralizer h54 ht1K ht1ord)
  have hcenter := h3 ↥X hcovX ⟨t1, ht1X⟩ htt htt2 ⟨z, hzX⟩ hw2 hwc hcard hcon
  refine false_of_center_eq htt2 htt hw2 hcenter (s := ⟨t, htX⟩) ?_ ?_ ?_ ?_ ?_ ?_
  · exact mem_centralizer_singleton_iff.2 (Subtype.ext hzt.symm)
  · intro y hy
    have hyz : (y : G) * z = z * (y : G) :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)
    have hyK : (y : G) ∈ centZ z := mem_centralizer_singleton_iff.2 hyz
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hle hyK))
  · intro h1
    have : t = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at ht2
    exact absurd ht2 (by decide)
  · exact fun h1 => hzne (congrArg Subtype.val h1).symm
  · exact fun h1 => hgt (congrArg Subtype.val h1).symm
  · intro h1
    have h2 : t = z * t1 := congrArg Subtype.val h1
    have h3' : t1 = z * t := by
      calc t1 = (z * z) * t1 := by rw [d.z_mul_self, one_mul]
        _ = z * (z * t1) := by rw [mul_assoc]
        _ = z * t := by rw [← h2]
    exact ht1pair (h3' ▸ mul_mem (mem_sup_left (mem_zpowers z)) (mem_sup_right (mem_zpowers t)))

end Certified

end CFSG.EvenSporadicStandard.TwoB
