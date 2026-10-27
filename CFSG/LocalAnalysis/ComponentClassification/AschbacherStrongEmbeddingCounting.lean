module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingConfine

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] {H : Subgroup G} {z : G}

theorem odd_card_of_involutive_unique_fixed {α : Type*} [Finite α] (f : α → α)
    (hf : ∀ a, f (f a) = a) (a₀ : α) (hfix : ∀ a, f a = a ↔ a = a₀) : Odd (Nat.card α) := by
  classical
  let := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Function.End α := f
  have hF : F ^ 2 ^ 1 = 1 := by
    funext a
    exact hf a
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hF
  have hone : Fintype.card (Function.fixedPoints F) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨a₀, (hfix a₀).mpr rfl⟩, fun a => Subtype.ext ((hfix a.1).mp a.2)⟩
  rw [hone] at hmod
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  exact hmod

theorem flipFiber_base_eq (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) :
    flipFiber z (QuotientGroup.mk 1 : G ⧸ H) (QuotientGroup.mk 1) = conjugacyWithin H z := by
  ext t
  constructor
  · rintro ⟨hconj, hfix⟩
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    have hc : c⁻¹ ∈ H := by
      have hmem := class_mem_iff_fixes_base.mpr hfix
      rw [← conj_mem_iff huniq c⁻¹]
      simpa only [inv_inv] using hmem
    exact ⟨⟨c⁻¹, hc⟩, by simp only [inv_inv]⟩
  · rintro ⟨h, rfl⟩
    refine ⟨isConj_iff.mpr ⟨(h : G)⁻¹, by simp only [inv_inv]⟩, ?_⟩
    exact class_mem_iff_fixes_base.mp (H.mul_mem (H.mul_mem (H.inv_mem h.property)
      (mem_of_unique huniq)) h.property)

theorem conjugacyWithin_card_mul_centralizer
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) [Finite H] :
    Nat.card (conjugacyWithin H z) * Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card H := by
  let zH : H := ⟨z, mem_of_unique huniq⟩
  have hsmall := conjugacy_class_card_mul_centralizer zH
  rw [Nat.card_congr (conjugacyWithinEquiv H zH)] at hsmall
  have hcentralizer : Nat.card (Subgroup.centralizer ({zH} : Set H)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    have heq : (Subgroup.centralizer ({zH} : Set H)).map H.subtype =
        Subgroup.centralizer ({z} : Set G) := by
      ext g
      constructor
      · rintro ⟨gH, hgH, rfl⟩
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hgH)
      · intro hg
        refine ⟨⟨g, centralizer_le_of_unique huniq hg⟩, ?_, rfl⟩
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg)
    rw [← heq, Subgroup.card_map_of_injective H.subtype_injective]
  rwa [hcentralizer] at hsmall

theorem class_card_eq_index_mul [Finite G] (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) :
    Nat.card (conjugatesOf z) = Nat.card (G ⧸ H) * Nat.card (conjugacyWithin H z) := by
  have hsmall := conjugacyWithin_card_mul_centralizer huniq
  have hbig := conjugacy_class_card_mul_centralizer z
  apply Nat.mul_right_cancel (Nat.card_pos (α := Subgroup.centralizer ({z} : Set G)))
  rw [hbig, mul_assoc, hsmall]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup H

theorem class_mem_of_isConj {t : G} (h : IsConj z t) : t ∈ involutionPointClass z := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact ⟨c⁻¹, by simp only [rightConjugateElem, inv_inv]⟩

theorem conjugacyWithin_card_odd [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (hH : H ≠ ⊤)
    (h1 : ProductUniqueContainment H z) : Odd (Nat.card (conjugacyWithin H z)) := by
  let base : G ⧸ H := QuotientGroup.mk 1
  have hstab : MulAction.stabilizer G base = H := CFSG.BenderSuzuki.baseCoset_stabilizer H
  have hconfine : ∀ t s : G, IsConj z t → IsConj z s → t * s ≠ 1 →
      t * s ∈ Subgroup.centralizer ({z} : Set G) →
        t ∈ MulAction.stabilizer G base ∧ s ∈ MulAction.stabilizer G base := by
    intro t s ht hs hne hcent
    rw [hstab]
    exact factors_mem_of_product_centralizing hz huniq h1 (class_mem_of_isConj ht)
      (class_mem_of_isConj hs) hne (Subgroup.mem_centralizer_singleton_iff.mp hcent)
  have huniform := uniform_flip_fiber_cards base z hz hconfine
    (by rw [hstab]; exact congrArg Nat.card (congrArg Set.Elem (flipFiber_base_eq huniq)))
    (by rw [hstab]; exact class_card_eq_index_mul huniq)
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    exact hH (eq_top_iff.mpr fun g _ => not_not.mp (not_exists.mp h g))
  let b : G ⧸ H := QuotientGroup.mk g
  have hb : b ≠ base := fun h => hg ((mk_eq_base_iff g).mp h)
  have hcard := huniform b
  rw [hstab] at hcard
  rw [← hcard]
  have hzmem : z ∈ conjugacyWithin H z := ⟨1, by simp only [OneMemClass.coe_one, inv_one,
    one_mul, mul_one]⟩
  have hpos : 0 < Nat.card (flipFiber z base b) := by
    rw [hcard]
    exact Nat.card_pos_iff.mpr ⟨⟨⟨z, hzmem⟩⟩, inferInstance⟩
  obtain ⟨⟨t₀, ht₀⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  have ht₀cls := class_mem_of_isConj ht₀.1
  have ht₀t₀ := class_mul_self hz ht₀cls
  have ht₀inv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_left ht₀t₀
  have ht₀b : t₀ • b = base := involution_flips_pair (class_orderOf hz ht₀cls) ht₀.2
  have hmem : ∀ s ∈ flipFiber z base b, t₀ * s * t₀ ∈ flipFiber z base b := by
    intro s hs
    refine ⟨hs.1.trans (isConj_iff.mpr ⟨t₀, by rw [ht₀inv]⟩), ?_⟩
    have hsb : s • b = base := involution_flips_pair (class_orderOf hz (class_mem_of_isConj hs.1))
      hs.2
    rw [mul_smul, mul_smul, ht₀.2, hsb, ht₀.2]
  apply odd_card_of_involutive_unique_fixed (α := flipFiber z base b)
    (fun s => ⟨t₀ * s.1 * t₀, hmem s.1 s.2⟩) _ ⟨t₀, ht₀⟩
  · intro s
    rw [Subtype.ext_iff, Subtype.ext_iff]
    change t₀ * s.1 * t₀ = s.1 ↔ s.1 = t₀
    constructor
    · intro hfix
      by_contra hne
      have hscls := class_mem_of_isConj s.2.1
      have hcomm : Commute t₀ s.1 := by
        change t₀ * s.1 = s.1 * t₀
        calc t₀ * s.1 = t₀ * s.1 * t₀ * t₀ := by rw [mul_assoc _ t₀, ht₀t₀, mul_one]
          _ = s.1 * t₀ := by rw [hfix]
      have hne' : s.1 ≠ t₀ := hne
      have hprod := product_smul_eq_iff huniq h1 ht₀cls hscls hcomm hne' base
      have hsb : s.1 • base = b := s.2.2
      have hfixbase : (t₀ * s.1) • base = base := by rw [mul_smul, hsb, ht₀b]
      exact hb (ht₀.2.symm.trans (hprod.mp hfixbase))
    · intro h
      rw [h, mul_assoc, ht₀t₀, mul_one]
  · intro s
    apply Subtype.ext
    change t₀ * (t₀ * s.1 * t₀) * t₀ = s.1
    rw [← mul_assoc, ← mul_assoc, ht₀t₀, one_mul, mul_assoc, ht₀t₀, mul_one]

end CFSG.ComponentClassification.AschbacherStrongEmbedding
