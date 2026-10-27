module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXSetup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoComponent

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.BenderSuzuki.PFAppendixIII

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace EscapingLift

theorem fusionStronglyEmbedded_of_forall (hu : EscapingLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z)
    (hno : ∀ w : J, (w : J ⧸ Subgroup.center J) ∈
      localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J) →
        w * w ≠ centralElt J) :
    fusionStronglyEmbedded ((B.map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
      (localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J))) := by
  set Bb := B.map (QuotientGroup.mk' (Subgroup.center J)) with hBb
  set Lu := localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J)
    with hLu
  refine ⟨fun htop => hu.hull_not_le h hz (Subgroup.subgroupOf_eq_top.mp htop), ?_, ?_⟩
  · have hzL : (z : J ⧸ Subgroup.center J) ∈ Lu :=
      distinguished_mem_localInvolutionPointHull hu.commute
    exact even_card_of_orderOf_eq_two (K := Bb.subgroupOf Lu) (t := ⟨_, hzL⟩)
      (Subgroup.mem_subgroupOf.mpr (hz.mk_mem_map h))
      (by rw [Subgroup.orderOf_mk]; exact hz.orderOf_mk)
  · intro g hg
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
    obtain ⟨hwB, hwconj⟩ := w.2
    obtain ⟨m, hmB, hmw⟩ := Subgroup.mem_map.mp hwconj
    have hw2 : orderOf (((w : Lu) : J ⧸ Subgroup.center J)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective ((w : Lu) : J ⧸ Subgroup.center J)
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective ((g : Lu) : J ⧸ Subgroup.center J)
    have haL : (a : J ⧸ Subgroup.center J) ∈ Lu := ha ▸ (w : Lu).2
    have haZ : a * a ∈ Subgroup.center J := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ha, ← hw2,
        pow_orderOf_eq_one]
    have ha1 : a * a = 1 := (h.mem_center_iff.mp haZ).resolve_right (hno a haL)
    have haZ' : a ∉ Subgroup.center J := by
      intro haZ'
      have h1 : (a : J ⧸ Subgroup.center J) = 1 := (QuotientGroup.eq_one_iff a).mpr haZ'
      rw [ha] at h1
      rw [h1, orderOf_one] at hw2
      exact absurd hw2 (by decide)
    have ha2 : orderOf a = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact ha1) fun h' =>
        haZ' (h' ▸ (Subgroup.center J).one_mem)
    have haB : a ∈ B := by
      rw [← h.mk_mem_map_iff, ha]
      exact Subgroup.mem_subgroupOf.mp hwB
    have hbaB : b * a * b⁻¹ ∈ B := by
      rw [← h.mk_mem_map_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        ha, hb]
      have hm : (m : Lu) = g * (w : Lu) * g⁻¹ := by
        rw [← hmw]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      have hmB' := Subgroup.mem_subgroupOf.mp hmB
      rw [hm] at hmB'
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmB'
    have hbB := h.mem_of_conj_mem haB ha2 haZ' hbaB
    apply hg
    rw [Subgroup.mem_subgroupOf, ← hb]
    exact (h.mk_mem_map_iff b).mpr hbB

theorem mem_of_mk_mem_hull (hu : EscapingLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    {W : Subgroup J} (hW : ∀ t ∈ quasiNormalizer u, orderOf t = 2 → t ∈ W) {w : J}
    (hw : (w : J ⧸ Subgroup.center J) ∈
      localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J)) :
    w ∈ W := by
  have heW : centralElt J ∈ W :=
    hW _ (h.centralElt_mem_quasiNormalizer u) h.orderOf_centralElt
  have hZW : Subgroup.center J ≤ W := fun c hc => by
    rcases h.mem_center_iff.mp hc with rfl | rfl
    · exact W.one_mem
    · exact heW
  have hle : localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J) ≤
      W.map (QuotientGroup.mk' (Subgroup.center J)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨g, rfl⟩, hyc⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have hy : rightConjugateElem (z : J ⧸ Subgroup.center J) (x : J ⧸ Subgroup.center J) =
        ((x⁻¹ * z * x : J) : J ⧸ Subgroup.center J) := by
      simp only [rightConjugateElem, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    refine ⟨x⁻¹ * z * x, hW _ ?_ ((orderOf_inv_mul_mul x z).trans hz.order), hy.symm⟩
    rw [hu.mem_quasiNormalizer_iff h, ← hy]
    exact Subgroup.mem_centralizer_singleton_iff.mp hyc
  obtain ⟨w', hw'W, hw'⟩ := hle hw
  have hww' : w'⁻¹ * w ∈ Subgroup.center J := QuotientGroup.eq.mp hw'
  simpa using W.mul_mem hw'W (hZW hww')

theorem fusionStronglyEmbedded_of_le (hu : EscapingLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) {W : Subgroup J} (hW : ∀ t ∈ quasiNormalizer u, orderOf t = 2 → t ∈ W)
    (hWsq : ∀ w ∈ W, w * w ≠ centralElt J) :
    fusionStronglyEmbedded ((B.map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
      (localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J))) :=
  hu.fusionStronglyEmbedded_of_forall h hz fun w hw => hWsq w (hu.mem_of_mk_mem_hull h hz hW hw)

theorem fusionStronglyEmbedded_of_quotient (hu : EscapingLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) {N : Subgroup (quasiNormalizer u)} [N.Normal]
    {H : Subgroup (quasiNormalizer u ⧸ N)}
    (hH : ∀ t : quasiNormalizer u, orderOf t = 2 → QuotientGroup.mk' N t ∈ H)
    (hsq : ∀ x ∈ H, x * x ≠ QuotientGroup.mk' N (quasiSelf u * quasiSelf u)) :
    fusionStronglyEmbedded ((B.map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
      (localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J))) := by
  refine hu.fusionStronglyEmbedded_of_le h hz
    (W := (H.comap (QuotientGroup.mk' N)).map (quasiNormalizer u).subtype) ?_ ?_
  · intro t ht ht2
    exact ⟨⟨t, ht⟩, hH ⟨t, ht⟩ (by rw [Subgroup.orderOf_mk]; exact ht2), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ hxx
    refine hsq _ hx ?_
    rw [← map_mul]
    congr 1
    exact Subtype.ext (hxx.trans hu.sq.symm)

theorem fusionStronglyEmbedded_of_quasiQuotient (hu : EscapingLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) {H : Subgroup (QuasiQuotient u)}
    (hH : ∀ t : quasiNormalizer u, orderOf t = 2 → quasiMk u t ∈ H)
    (hsq : ∀ x ∈ H, x * x ≠ quasiCentral u) :
    fusionStronglyEmbedded ((B.map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
      (localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J))) :=
  hu.fusionStronglyEmbedded_of_quotient h hz hH fun x hx => by
    rw [map_mul]
    exact hsq x hx

end EscapingLift

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
