module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTheorem
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote.L54

open Subgroup CFSG.ComponentClassification.AschbacherStrongEmbedding CFSG.ShultStronglyClosedTI
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G]

theorem not_forall_commute_of_card_eight [Finite G] (hs : IsSimpleGroup G) {E : Subgroup G}
    (hE8 : Nat.card E = 8) {t : G} (ht : orderOf t = 2) : ¬ ∀ g : G, g * t = t * g := by
  intro hcen
  have := hs
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht; omega
  have hn : (zpowers t).Normal :=
    normal_of_le_center (zpowers_le.mpr (mem_center_iff.mpr hcen))
  rcases hn.eq_bot_or_eq_top with h | h
  · have h1 := mem_zpowers t
    rw [h, mem_bot] at h1
    exact ht1 h1
  · have h1 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
    rw [h, card_top] at h1
    have h2 := E.card_le_card_group
    omega

theorem fusionStronglyEmbedded_of_puc [Finite G]
    (hs : IsSimpleGroup G) {E : Subgroup G} (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8)
    {H : Subgroup G} {z : G} (hz : orderOf z = 2) (hH : H ≠ ⊤)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (hP : ProductUniqueContainment H z) : CFSG.Open.fusionStronglyEmbedded H := by
  have := hs
  obtain ⟨h12, h23, -⟩ := theorem_3_3 not_minimalInvolutionPointLocalFailure
    benderDoubleCoverRigidity H z hz hH huniq
  have h3 := h23 (h12 hP)
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz; omega
  have hhull : involutionPointHull z = ⊤ := by
    rcases (minimalLocalFailure_hull_normal z).eq_bot_or_eq_top with h | h
    · exfalso
      apply hz1
      have h1 : z ∈ involutionPointHull z :=
        subset_closure ⟨1, by simp [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem]⟩
      rw [h, mem_bot] at h1
      exact h1
    · exact h
  have hcomm : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    rcases (commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      apply not_forall_commute_of_card_eight hs hE8 hz
      intro g
      have h1 : g * z * g⁻¹ * z⁻¹ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
        commutator_mem_commutator (mem_top g) (mem_top z)
      rw [h, mem_bot, mul_inv_eq_one] at h1
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h1]
    · exact h
  rcases h3 with hr | ⟨u, -, -, -, -, hse, -⟩
  · exfalso
    set K := involutionPointHull z with hK
    have hEK : E ≤ K := hhull ▸ le_top
    have hEel : CFSG.Open.IsElemAbelian 2 E := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => hE2 a ha⟩
      have hab : (a : G) * b * ((a : G) * b) = 1 := by
        simpa [pow_two] using hE2 _ (E.mul_mem a.2 b.2)
      have ha2 : (a : G) * a = 1 := by simpa [pow_two] using hE2 _ a.2
      have hb2 : (b : G) * b = 1 := by simpa [pow_two] using hE2 _ b.2
      have hai : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
      have hbi : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
      have : (a : G) * b = ((a : G) * b)⁻¹ := eq_inv_of_mul_eq_one_right hab
      rw [mul_inv_rev, hai, hbi] at this
      exact this
    have hel : CFSG.Open.IsElemAbelian 2 (E.subgroupOf K) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
      · have := hEel.1
        have ha' : (((a : ↥K) : G)) ∈ E := a.2
        have hb' : (((b : ↥K) : G)) ∈ E := b.2
        exact setLike_mul_comm ha' hb'
      · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE2 _ ha
    have hcard : Nat.card (E.subgroupOf K) = 2 ^ 3 := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hEK).symm.toEquiv, hE8]
      norm_num
    have h4 := SectionRank.le_pRank one_lt_two (le_top : E.subgroupOf K ≤ ⊤) hel hcard
    have h5 : CFSG.Open.twoRank ↥K ≤ 1 := hr
    unfold CFSG.Open.twoRank at h5
    omega
  · rw [hhull, hcomm] at hse
    have hmap := hse.map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    have himage : (H.subgroupOf (⊤ : Subgroup G)).map
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom = H := by
      change (H.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = H
      rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
    rwa [himage] at hmap

end CFSG.CGT.PushingUpLit.LIT.Foote.L54
