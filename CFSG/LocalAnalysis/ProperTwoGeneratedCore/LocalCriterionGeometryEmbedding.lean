module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

abbrev rightCosetSpace (H : Subgroup G) : Type u :=
  Quotient (QuotientGroup.rightRel H)

@[expose] def rightCosetMk (H : Subgroup G) (x : G) : rightCosetSpace H :=
  Quotient.mk (QuotientGroup.rightRel H) x

@[expose] def rightCosetTranslate (H : Subgroup G) (omega : rightCosetSpace H)
    (g : G) : rightCosetSpace H :=
  Quotient.map' (fun x : G => x * g) (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hab) omega

theorem rightCosetTranslate_mk (H : Subgroup G) (x g : G) :
    rightCosetTranslate H (rightCosetMk H x) g = rightCosetMk H (x * g) := rfl

theorem rightCosetTranslate_one (H : Subgroup G) (omega : rightCosetSpace H) :
    rightCosetTranslate H omega 1 = omega := by
  refine Quotient.inductionOn' omega fun x => ?_
  change rightCosetMk H (x * 1) = rightCosetMk H x
  rw [mul_one]

theorem rightCosetTranslate_mul (H : Subgroup G) (omega : rightCosetSpace H)
    (g k : G) :
    rightCosetTranslate H (rightCosetTranslate H omega g) k =
      rightCosetTranslate H omega (g * k) := by
  refine Quotient.inductionOn' omega fun x => ?_
  change rightCosetMk H ((x * g) * k) = rightCosetMk H (x * (g * k))
  rw [mul_assoc]

theorem rightCosetTranslate_inversion (H : Subgroup G) (omega : rightCosetSpace H)
    (g : G) :
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H
        (rightCosetTranslate H omega g) =
      g⁻¹ • QuotientGroup.quotientRightRelEquivQuotientLeftRel H omega := by
  refine Quotient.inductionOn' omega fun x => ?_
  change (QuotientGroup.mk ((x * g)⁻¹) : G ⧸ H) =
    QuotientGroup.mk (g⁻¹ * x⁻¹)
  rw [mul_inv_rev]

@[expose] def rightCosetStabilizer (H : Subgroup G) (omega : rightCosetSpace H) :
    Subgroup G :=
  MulAction.stabilizer G
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H omega)

theorem mem_rightCosetStabilizer_iff (H : Subgroup G) (omega : rightCosetSpace H)
    (g : G) :
    g ∈ rightCosetStabilizer H omega ↔ rightCosetTranslate H omega g = omega := by
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  change g • e omega = e omega ↔ rightCosetTranslate H omega g = omega
  constructor
  · intro hfix
    apply e.injective
    rw [rightCosetTranslate_inversion]
    simpa only [inv_smul_smul] using
      (congrArg (fun x : G ⧸ H => g⁻¹ • x) hfix).symm
  · intro hfix
    have hleft := congrArg e hfix
    rw [rightCosetTranslate_inversion] at hleft
    have h := congrArg (fun x : G ⧸ H => g • x) hleft
    simpa only [smul_inv_smul] using h.symm

theorem rightCosetStabilizer_base (H : Subgroup G) :
    rightCosetStabilizer H (rightCosetMk H 1) = H := by
  change MulAction.stabilizer G (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = H
  simpa only [inv_one] using baseCoset_stabilizer H

theorem rightCosetStabilizer_mk (H : Subgroup G) (x : G) :
    rightCosetStabilizer H (rightCosetMk H x) = rightConjugate H x := by
  change MulAction.stabilizer G (QuotientGroup.mk x⁻¹ : conjugateCosetSpace H) =
    rightConjugate H x
  simpa only [inv_inv] using conjugateCoset_stabilizer H x⁻¹

@[expose] def rightPairFlipFiber (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) : Set G :=
  {t | t ∈ involutionPointClass z ∧
    rightCosetTranslate H (rightCosetMk H 1) t = beta}

@[expose] def rightPairFlipProducts (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t₀ : G) : Set G :=
  (fun t : G => t * t₀) '' rightPairFlipFiber H z beta

private theorem pointClass_eq_conjugatesOf (z : G) :
    involutionPointClass z = conjugatesOf z := by
  rw [pointClass_eq_conjAct_orbit]
  ext t
  exact ConjAct.mem_orbit_conjAct.trans ⟨IsConj.symm, IsConj.symm⟩

private theorem mem_pointClass_iff_isConj (z t : G) :
    t ∈ involutionPointClass z ↔ IsConj z t := by
  change t ∈ involutionPointClass z ↔ t ∈ conjugatesOf z
  rw [pointClass_eq_conjugatesOf]

private theorem subgroupClass_eq_conjugacyWithin (H : Subgroup G) (z : G) :
    {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t} =
      conjugacyWithin H z := by
  ext t
  constructor
  · rintro ⟨g, hg, hgt⟩
    exact ⟨⟨g, hg⟩, hgt⟩
  · rintro ⟨g, hgt⟩
    exact ⟨g, g.property, hgt⟩

private theorem rightPairFlipFiber_eq_left (H : Subgroup G) (z : G)
    (hz : orderOf z = 2) (beta : rightCosetSpace H) :
    rightPairFlipFiber H z beta =
      flipFiber z (QuotientGroup.mk 1 : conjugateCosetSpace H)
        (QuotientGroup.quotientRightRelEquivQuotientLeftRel H beta) := by
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  have hbase : e (rightCosetMk H 1) = (QuotientGroup.mk 1 : G ⧸ H) := by
    change (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = QuotientGroup.mk 1
    rw [inv_one]
  ext t
  change (t ∈ involutionPointClass z ∧
    rightCosetTranslate H (rightCosetMk H 1) t = beta) ↔
    (IsConj z t ∧ t • (QuotientGroup.mk 1 : G ⧸ H) = e beta)
  constructor
  · rintro ⟨ht, htbeta⟩
    have htinv := inv_eq_self_of_orderOf_eq_two (order_two_of_mem_pointClass hz ht)
    refine ⟨(mem_pointClass_iff_isConj z t).mp ht, ?_⟩
    have hh := congrArg e htbeta
    rw [rightCosetTranslate_inversion, htinv, hbase] at hh
    exact hh
  · rintro ⟨ht, htbeta⟩
    have htclass : t ∈ involutionPointClass z :=
      (mem_pointClass_iff_isConj z t).mpr ht
    have htinv := inv_eq_self_of_orderOf_eq_two (order_two_of_mem_pointClass hz htclass)
    refine ⟨htclass, e.injective ?_⟩
    rw [rightCosetTranslate_inversion, htinv, hbase]
    exact htbeta

private theorem embedding_product_confinement [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) :
    ∀ t s : G, IsConj z t → IsConj z s → t * s ≠ 1 →
      t * s ∈ Subgroup.centralizer ({z} : Set G) →
        t ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : conjugateCosetSpace H) ∧
        s ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : conjugateCosetSpace H) := by
  intro t s ht hs hne hcentral
  rw [baseCoset_stabilizer]
  exact pointClass_factors_mem_of_product_centralizing h
    ((mem_pointClass_iff_isConj z t).mpr ht)
    ((mem_pointClass_iff_isConj z s).mpr hs) hne
    (Subgroup.mem_centralizer_singleton_iff.mp hcentral)

private theorem embedding_uniform_left_flip_fibers [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) :
    ∀ beta : conjugateCosetSpace H,
      Nat.card (flipFiber z (QuotientGroup.mk 1 : conjugateCosetSpace H) beta) =
        Nat.card (conjugacyWithin H z) := by
  let base : conjugateCosetSpace H := QuotientGroup.mk 1
  have hfixed : flipFiber z base base = conjugacyWithin H z := by
    ext t
    have hfix : t • base = base ↔ t ∈ H := by
      change t ∈ MulAction.stabilizer G base ↔ t ∈ H
      change t ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : conjugateCosetSpace H) ↔
        t ∈ H
      rw [baseCoset_stabilizer]
    change (IsConj z t ∧ t • base = base) ↔ t ∈ conjugacyWithin H z
    rw [hfix]
    change t ∈ conjugatesOf z ∩ (H : Set G) ↔ t ∈ conjugacyWithin H z
    rw [← pointClass_eq_conjugatesOf z, pointClass_inter_eq_subgroupClass h,
      subgroupClass_eq_conjugacyWithin]
  have hclass := pointClass_card_factorization h
  rw [pointClass_eq_conjugatesOf, subgroupClass_eq_conjugacyWithin,
    H.index_eq_card] at hclass
  have hh := uniform_flip_fiber_cards base z h.distinguished_order
    (embedding_product_confinement h)
    (by rw [baseCoset_stabilizer, hfixed])
    (by simpa only [base, baseCoset_stabilizer] using hclass)
  simpa only [base, baseCoset_stabilizer] using hh

theorem involution_point_uniform_pair_flips [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    Nat.card (rightPairFlipFiber H z beta) = Nat.card (conjugacyWithin H z) ∧
    (∀ t ∈ rightPairFlipFiber H z beta,
      rightCosetTranslate H beta t = rightCosetMk H 1) ∧
    (∀ t₀ ∈ rightPairFlipFiber H z beta,
      rightPairFlipProducts H z beta t₀ ⊆
        (rightCosetStabilizer H (rightCosetMk H 1) ⊓
          rightCosetStabilizer H beta : Subgroup G) ∧
      ∀ a : H, ∃! k : rightPairFlipProducts H z beta t₀,
        (k : G) ∈ MulOpposite.op (a : G) •
          (Subgroup.centralizer ({z} : Set G) : Set G)) := by
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  let base : conjugateCosetSpace H := QuotientGroup.mk 1
  have hbase : e (rightCosetMk H 1) = base := by
    change (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = QuotientGroup.mk 1
    rw [inv_one]
  have hbetaleft : e beta ≠ base := by
    intro heq
    exact hbeta (e.injective (heq.trans hbase.symm))
  have hfiber := rightPairFlipFiber_eq_left H z h.distinguished_order beta
  have hcard := embedding_uniform_left_flip_fibers h (e beta)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfiber]
    exact hcard
  · intro t ht
    have htleft : t ∈ flipFiber z base (e beta) := hfiber ▸ ht
    have htorder := order_two_of_mem_pointClass h.distinguished_order ht.1
    apply e.injective
    rw [rightCosetTranslate_inversion, inv_eq_self_of_orderOf_eq_two htorder, hbase]
    exact involution_flips_pair htorder htleft.2
  · intro t₀ ht₀
    have ht₀left : t₀ ∈ flipFiber z base (e beta) := hfiber ▸ ht₀
    have ht₀order := order_two_of_mem_pointClass h.distinguished_order ht₀.1
    refine ⟨?_, ?_⟩
    · rintro k ⟨t, ht, rfl⟩
      have htleft : t ∈ flipFiber z base (e beta) := hfiber ▸ ht
      have htorder := order_two_of_mem_pointClass h.distinguished_order ht.1
      change t * t₀ ∈ MulAction.stabilizer G (e (rightCosetMk H 1)) ⊓
        MulAction.stabilizer G (e beta)
      rw [hbase]
      exact flip_product_mem_two_point_stabilizer htorder ht₀order htleft.2 ht₀left.2
    · intro a
      have hcard' : Nat.card (flipFiber z base (e beta)) =
          Nat.card (conjugacyWithin (MulAction.stabilizer G base) z) := by
        simpa only [base, baseCoset_stabilizer] using hcard
      obtain ⟨t, ht, hunique⟩ := flip_products_class_map_bijective base (e beta) z
        h.distinguished_order hbetaleft (embedding_product_confinement h)
        hcard' t₀ ht₀left
        (⟨a, (baseCoset_stabilizer H).symm ▸ a.property⟩ : MulAction.stabilizer G base)
      have htright : (t : G) ∈ rightPairFlipFiber H z beta := hfiber.symm ▸ t.property
      refine ⟨⟨t.val * t₀, ⟨t.val, htright, rfl⟩⟩,
        (mem_rightCoset_iff (s := (Subgroup.centralizer ({z} : Set G) : Set G))
          (a : G)).mpr ht,
        ?_⟩
      rintro ⟨k, s, hs, hsk⟩ hkcoset
      change s * t₀ = k at hsk
      change k ∈ MulOpposite.op (a : G) •
        (Subgroup.centralizer ({z} : Set G) : Set G) at hkcoset
      have hsleft : s ∈ flipFiber z base (e beta) := hfiber ▸ hs
      have hscoset : s * t₀ * (a : G)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [hsk]
        exact (mem_rightCoset_iff
          (s := (Subgroup.centralizer ({z} : Set G) : Set G)) (a : G)).mp hkcoset
      have heq := congrArg Subtype.val (hunique ⟨s, hsleft⟩ hscoset)
      change s = t.val at heq
      apply Subtype.ext
      change k = t.val * t₀
      rw [← hsk, heq]

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
