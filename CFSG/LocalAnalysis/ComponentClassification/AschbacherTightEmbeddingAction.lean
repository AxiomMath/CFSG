module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingProducts
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionStrictEmbedding

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

theorem overlap_with_two_subgroup_eq {G : Type*} [Group G] [Finite G]
    (P Q T S : Subgroup G) (hodd : Odd (Nat.card ↥(P ⊓ Q)))
    (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G)) (hTP : T ≤ P)
    (hTS : T ≤ S) (hS : S ≤ Q ⊔ T) (htwoS : IsPGroup 2 S) :
    P ⊓ S = T := by
  have hbot : (P ⊓ S) ⊓ Q = ⊥ :=
    two_subgroup_of_odd_eq_bot ((P ⊓ S) ⊓ Q) (P ⊓ Q)
      (htwoS.to_le (inf_le_left.trans inf_le_right)) hodd
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  apply le_antisymm _ (le_inf hTP hTS)
  intro x hx
  obtain ⟨q, hq, t, ht, heq⟩ := NormalizedProduct.coordinates Q T hnormalizes x (hS hx.2)
  have hqP : q ∈ P := by
    have hmem := P.mul_mem hx.1 (P.inv_mem (hTP ht))
    rw [← heq, mul_inv_cancel_right] at hmem
    exact hmem
  have hqS : q ∈ S := by
    have hmem := S.mul_mem hx.2 (S.inv_mem (hTS ht))
    rw [← heq, mul_inv_cancel_right] at hmem
    exact hmem
  have hqOne : q = 1 := Subgroup.mem_bot.mp
    (hbot ▸ (show q ∈ (P ⊓ S) ⊓ Q from ⟨⟨hqP, hqS⟩, hq⟩))
  rw [hqOne, one_mul] at heq
  exact heq ▸ ht

theorem complement_centralizers_le_normalizer {G : Type*} [Group G] [Finite G]
    (P Q T S : Subgroup G) (htight : TightlyEmbedded P)
    (hodd : Odd (Nat.card ↥(P ⊓ Q)))
    (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G)) (hTP : T ≤ P)
    (hTS : T ≤ S) (hS : S ≤ Q ⊔ T) (htwoS : IsPGroup 2 S) :
    ∀ t ∈ T, t ≠ 1 → Subgroup.centralizer {t} ⊓ (S ⊓ Q) ≤
      relativeNormalizer T S ⊓ Q := by
  intro t ht hne x hx
  let cyclic := Subgroup.zpowers t
  have htwo : IsPGroup 2 cyclic := htwoS.to_le (Subgroup.zpowers_le.mpr (hTS ht))
  have hcyclic : cyclic ≤ P := Subgroup.zpowers_le.mpr (hTP ht)
  have hcyclicNe : cyclic ≠ ⊥ := by
    intro hbot
    exact hne (Subgroup.zpowers_eq_bot.mp hbot)
  have hxP : x ∈ Subgroup.normalizer (P : Set G) := by
    apply centralizer_two_subgroup_le P cyclic htight htwo hcyclic hcyclicNe
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨n, rfl⟩ := hy
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hx.1) n).symm
  have hxPS : x ∈ Subgroup.normalizer ((P ⊓ S : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hxP, Subgroup.le_normalizer hx.2.1⟩
  rw [overlap_with_two_subgroup_eq P Q T S hodd hnormalizes hTP hTS hS htwoS] at hxPS
  exact ⟨⟨hxPS, hx.2.1⟩, hx.2.2⟩

theorem complement_normalizer_alternative {G : Type*} [Group G] [Finite G]
    (P Q T S : Subgroup G) (htight : TightlyEmbedded P)
    (hodd : Odd (Nat.card ↥(P ⊓ Q)))
    (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G)) (hTP : T ≤ P)
    (hTS : T ≤ S) (hS : S ≤ Q ⊔ T) (htwoS : IsPGroup 2 S) :
    S ≤ Subgroup.normalizer (T : Set G) ∨
      ∃ homomorphism : T →* Subgroup.center ↥(relativeNormalizer T S ⊓ Q),
        Function.Injective homomorphism := by
  classical
  let base := S ⊓ Q
  let fixed := relativeNormalizer T S ⊓ Q
  have htwoT : IsPGroup 2 T := htwoS.to_le hTS
  have hdisjointT : Disjoint T Q := by
    apply disjoint_iff.mpr
    exact two_subgroup_of_odd_eq_bot (T ⊓ Q) (P ⊓ Q)
      (htwoT.to_le inf_le_left) hodd (le_inf (inf_le_left.trans hTP) inf_le_right)
  have hfixedBase : fixed ≤ base := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hcentral : T ≤ Subgroup.centralizer (fixed : Set G) := by
    intro t ht
    exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (relativeNormalizer_factors_commute Q T S hnormalizes hdisjointT t ht q hq).symm
  have hnormalizesBase : T ≤ Subgroup.normalizer (base : Set G) := by
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hTS ht), hnormalizes ht⟩
  by_cases hnormal : S ≤ Subgroup.normalizer (T : Set G)
  · exact Or.inl hnormal
  have hfixedProper : fixed < base := by
    apply lt_of_le_of_ne hfixedBase
    intro hfixedEq
    apply hnormal
    intro x hx
    obtain ⟨q, hq, t, ht, heq⟩ := NormalizedProduct.coordinates Q T hnormalizes x (hS hx)
    have hqS : q ∈ S := by
      have hmem := S.mul_mem hx (S.inv_mem (hTS ht))
      rw [← heq, mul_inv_cancel_right] at hmem
      exact hmem
    have hqFixed : q ∈ fixed := hfixedEq ▸ (show q ∈ base from ⟨hqS, hq⟩)
    rw [← heq]
    exact (Subgroup.normalizer (T : Set G)).mul_mem hqFixed.1.1 (Subgroup.le_normalizer ht)
  have hdisjointBase : Disjoint base T := hdisjointT.symm.mono_left inf_le_right
  obtain ⟨actor, hactor, houtside, hproduct⟩ :=
    TwoActionStrictEmbedding.escape base T fixed fixed base hfixedBase le_rfl
      (htwoS.to_le inf_le_left) htwoT hdisjointBase hcentral hnormalizesBase
      (inf_eq_left.mpr hfixedBase) hfixedProper
  exact Or.inr (TwoActionDisplacementEmbedding.embedding base T fixed fixed hfixedBase
    hdisjointBase hnormalizesBase hcentral
    (complement_centralizers_le_normalizer P Q T S htight hodd hnormalizes hTP hTS hS htwoS)
      actor hactor houtside hproduct)

theorem complement_normal_of_small_index {G : Type*} [Group G] [Finite G]
    (P Q T X : Subgroup G) (htight : TightlyEmbedded P)
    (hodd : Odd (Nat.card ↥(P ⊓ Q)))
    (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G)) (hTP : T ≤ P)
    (hTX : T ≤ X) (hX : X ≤ Q ⊔ T) (htwoX : IsPGroup 2 X)
    (hindex : (T.subgroupOf X).index ≤ Nat.card T) :
    X ≤ Subgroup.normalizer (T : Set G) := by
  rcases complement_normalizer_alternative P Q T X htight hodd hnormalizes hTP hTX hX htwoX
    with hnormal | ⟨homomorphism, hinjective⟩
  · exact hnormal
  have hcardT : Nat.card T ≤ Nat.card ↥(relativeNormalizer T X ⊓ Q) := by
    have hcenter := Nat.card_le_card_of_injective homomorphism hinjective
    exact hcenter.trans (Subgroup.card_le_card_group _)
  have hdisjoint : Disjoint T Q := by
    apply disjoint_iff.mpr
    exact two_subgroup_of_odd_eq_bot (T ⊓ Q) (P ⊓ Q)
      ((htwoX.to_le hTX).to_le inf_le_left) hodd
      (le_inf (inf_le_left.trans hTP) inf_le_right)
  have hnormalizerCard := relativeNormalizer_card Q T X hnormalizes hdisjoint hTX hX
  have hXCard : Nat.card X = Nat.card T * (T.subgroupOf X).index := by
    have h := (T.subgroupOf X).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv] at h
    exact h.symm
  have hcardLe : Nat.card X ≤ Nat.card (relativeNormalizer T X) := by
    rw [hXCard, hnormalizerCard]
    exact Nat.mul_le_mul_left _ (hindex.trans hcardT)
  have hnormalizerEq : relativeNormalizer T X = X :=
    Subgroup.eq_of_le_of_card_ge inf_le_right hcardLe
  intro x hx
  have hmem : x ∈ relativeNormalizer T X := by rw [hnormalizerEq]; exact hx
  exact hmem.1

theorem complement_small_index_literal_normal {G : Type*} [Group G] [Finite G]
    (P Q T X : Subgroup G) (htight : TightlyEmbedded P)
    (hodd : Odd (Nat.card ↥(P ⊓ Q)))
    (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G)) (hTP : T ≤ P)
    (hTX : T ≤ X) (hX : X ≤ Q ⊔ T) (htwoX : IsPGroup 2 X)
    (hindex : (T.subgroupOf X).index ≤ Nat.card T) :
    (T.subgroupOf X).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (complement_normal_of_small_index P Q T X htight hodd hnormalizes hTP hTX hX htwoX hindex)

end CFSG.ComponentClassification.AschbacherTightEmbedding
