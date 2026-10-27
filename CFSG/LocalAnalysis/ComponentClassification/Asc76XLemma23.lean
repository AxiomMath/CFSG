module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf {X N : Subgroup G} (hXN : X ≤ normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) =
      Nat.card X * Nat.card N := by
  have : (N.subgroupOf (X ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have : (N.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem exists_mem_normalizer_not_mem [Finite G] {p : ℕ} [Fact p.Prime] {X N : Subgroup G}
    (hX : IsPGroup p X) (hNX : N ≤ X) (hne : ¬ X ≤ N) :
    ∃ x ∈ X, x ∉ N ∧ x ∈ normalizer (N : Set G) := by
  have hnil : Group.IsNilpotent X := hX.isNilpotent
  have hlt : N.subgroupOf X < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne fun x hx => ?_
    have : (⟨x, hx⟩ : X) ∈ N.subgroupOf X := h ▸ mem_top _
    exact mem_subgroupOf.1 this
  obtain ⟨y, hy, hyN⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨y, y.2, fun h => hyN (mem_subgroupOf.2 h), ?_⟩
  rw [mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have hnX : n ∈ X := hNX hn
    have := (mem_normalizer_iff.1 hy ⟨n, hnX⟩).1 (mem_subgroupOf.2 hn)
    simpa [mem_subgroupOf] using this
  · intro hn
    have hnX : n ∈ X := by
      have h1 : (y : G) * n * (y : G)⁻¹ ∈ X := hNX hn
      have : n = (y : G)⁻¹ * ((y : G) * n * (y : G)⁻¹) * y := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem y.2) h1) y.2
    have := (mem_normalizer_iff.1 hy ⟨n, hnX⟩).2 (by
      rw [mem_subgroupOf]
      simpa using hn)
    exact mem_subgroupOf.1 this

theorem normalizes_of_card_le [Finite G] {R X : Subgroup G} (hX : IsPGroup 2 X) (hRX : R ≤ X)
    (hTI : ∀ x ∈ X, x ∉ normalizer (R : Set G) → R ⊓ rightConjugate R x = ⊥)
    (hcard : Nat.card X ≤ Nat.card R * Nat.card R) : X ≤ normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hXN
  set N := X ⊓ normalizer (R : Set G) with hNdef
  have hNX : N ≤ X := inf_le_left
  have hne : ¬ X ≤ N := fun h => hXN (h.trans inf_le_right)
  obtain ⟨x, hxX, hxN, hxNN⟩ := exists_mem_normalizer_not_mem hX hNX hne
  have hxR : x ∉ normalizer (R : Set G) := fun h => hxN ⟨hxX, h⟩
  have hRN : R ≤ N := le_inf hRX le_normalizer
  have hRxN : rightConjugate R x ≤ N := fun y hy => by
    rw [mem_rightConjugate_iff] at hy
    exact (mem_normalizer_iff.1 hxNN y).2 (hRN hy)
  have hRxNR : rightConjugate R x ≤ normalizer (R : Set G) := hRxN.trans inf_le_right
  have hRxX : rightConjugate R x ≤ X := hRxN.trans hNX
  have hinf : rightConjugate R x ⊓ R = ⊥ := by rw [inf_comm]; exact hTI x hxX hxR
  have hprod := card_sup_mul_card_inf hRxNR
  rw [hinf, card_bot, mul_one, rightConjugate_card] at hprod
  have hle : rightConjugate R x ⊔ R ≤ X := sup_le hRxX hRX
  have heq : rightConjugate R x ⊔ R = X :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hprod, mul_comm]; exact hcard)
  apply hXN
  rw [← heq]
  exact sup_le hRxNR le_normalizer

theorem lemma23 [Finite G] {S R T : Subgroup G} (hS : IsPGroup 2 S) (hRS : R ≤ S)
    (hR : TightlyEmbedded (R.subgroupOf S)) (hTS : T ≤ S) (hRT : R ≤ normalizer (T : Set G))
    (hcard : Nat.card T ≤ Nat.card R) (hRT1 : R ⊓ T = ⊥) : ⁅R, T⁆ = ⊥ := by
  set X := R ⊔ T with hXdef
  have hXS : X ≤ S := sup_le hRS hTS
  have hX : IsPGroup 2 X := hS.to_le hXS
  have hprod := card_sup_mul_card_inf hRT
  rw [hRT1, card_bot, mul_one] at hprod
  have hXcard : Nat.card X ≤ Nat.card R * Nat.card R := by
    rw [hXdef, hprod]
    exact Nat.mul_le_mul_left _ hcard
  have hTI : ∀ x ∈ X, x ∉ normalizer (R : Set G) → R ⊓ rightConjugate R x = ⊥ := by
    intro x hxX hxR
    have hxS : x ∈ S := hXS hxX
    have hxN : (⟨x, hxS⟩ : S) ∉ normalizer ((R.subgroupOf S : Subgroup S) : Set S) := by
      intro h
      apply hxR
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have := (mem_normalizer_iff.1 h ⟨y, hRS hy⟩).1 (mem_subgroupOf.2 hy)
        simpa [mem_subgroupOf] using this
      · intro hy
        have hyS : y ∈ S := by
          have h1 : x * y * x⁻¹ ∈ S := hRS hy
          have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
          rw [this]
          exact mul_mem (mul_mem (inv_mem hxS) h1) hxS
        have := (mem_normalizer_iff.1 h ⟨y, hyS⟩).2 (by
          rw [mem_subgroupOf]
          simpa using hy)
        exact mem_subgroupOf.1 this
    have hodd := hR.2 _ hxN
    have hbot := two_subgroup_of_odd_eq_bot _ _ (hS.to_subgroup _) hodd le_rfl
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyR, hyRx⟩ := mem_inf.1 hy
    have hyS : y ∈ S := hRS hyR
    have hmem : (⟨y, hyS⟩ : S) ∈ R.subgroupOf S ⊓ rightConjugate (R.subgroupOf S) ⟨x, hxS⟩ := by
      refine mem_inf.2 ⟨mem_subgroupOf.2 hyR, ?_⟩
      rw [mem_rightConjugate_iff, mem_subgroupOf]
      rw [mem_rightConjugate_iff] at hyRx
      simpa using hyRx
    rw [hbot, mem_bot] at hmem
    rw [mem_bot]
    exact congrArg Subtype.val hmem
  have hXN := normalizes_of_card_le hX le_sup_left hTI hXcard
  rw [eq_bot_iff, commutator_le]
  intro r hr t ht
  have hcomm : r * t * r⁻¹ * t⁻¹ ∈ R ⊓ T := by
    refine mem_inf.2 ⟨?_, ?_⟩
    · have h1 : t * r⁻¹ * t⁻¹ ∈ R :=
        (mem_normalizer_iff.1 (hXN (mem_sup_right ht)) r⁻¹).1 (inv_mem hr)
      have : r * t * r⁻¹ * t⁻¹ = r * (t * r⁻¹ * t⁻¹) := by group
      rw [this]
      exact mul_mem hr h1
    · have h1 : r * t * r⁻¹ ∈ T := (mem_normalizer_iff.1 (hRT hr) t).1 ht
      exact mul_mem h1 (inv_mem ht)
  rw [hRT1] at hcomm
  rw [commutatorElement_def]
  exact hcomm

end CFSG.ComponentClassification.Asc76X
