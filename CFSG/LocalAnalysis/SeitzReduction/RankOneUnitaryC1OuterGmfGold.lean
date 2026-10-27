module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterHighGold
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem gmf_map_centralizer_inf {K A : Subgroup G} (hAK : A ≤ K) (B' : Subgroup K) :
    ((centralizer ((A.subgroupOf K : Subgroup K) : Set K)) ⊓ B').map K.subtype =
      B'.map K.subtype ⊓ centralizer (A : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxC, hxB⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨⟨x, hxB, rfl⟩, mem_centralizer_iff.mpr fun a ha => ?_⟩
    have h1 := mem_centralizer_iff.mp hxC ⟨a, hAK ha⟩ (mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h1
  · intro hy
    obtain ⟨⟨x, hxB, rfl⟩, hyC⟩ := mem_inf.mp hy
    refine ⟨x, mem_inf.mpr ⟨mem_centralizer_iff.mpr fun a ha => ?_, hxB⟩, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.mp hyC (a : G) (mem_subgroupOf.mp ha))

omit [Finite G] in
theorem gmf_map_centralizer_singleton_inf {K A : Subgroup G} (hAK : A ≤ K) (x : K) :
    ((centralizer ({x} : Set K)) ⊓ A.subgroupOf K).map K.subtype =
      A ⊓ centralizer ({(x : G)} : Set G) := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨haC, haA⟩ := mem_inf.mp ha
    refine mem_inf.mpr ⟨mem_subgroupOf.mp haA, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp haC)
  · intro hy
    obtain ⟨hyA, hyC⟩ := mem_inf.mp hy
    refine ⟨⟨y, hAK hyA⟩, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
      mem_subgroupOf.mpr hyA⟩, rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hyC)

theorem gmf_cor4_self_rel {K S A : Subgroup G} (hS : IsSylowOf 2 S K) (hAS : A ≤ S)
    (hwc : ∀ g ∈ K, (∀ a ∈ A, g * a * g⁻¹ ∈ S) → ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    (∀ a ∈ A, ∀ g ∈ K, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ A) ∨
      ∀ x ∈ S, x ∉ A → (∃ g ∈ K, g * x * g⁻¹ ∈ A) →
        ∃ B : Subgroup G, B ≤ S ∧ ¬ B ≤ A ∧ (∃ g ∈ K, ∀ b ∈ B, g * b * g⁻¹ ∈ A) ∧
          Nat.card A * Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) ≤
            Nat.card B * Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) ∧
          Nat.card A * Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) ≤
            Nat.card B * Nat.card B := by
  have hSK : S ≤ K := hS.le
  have hAK : A ≤ K := hAS.trans hSK
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  set A' : Subgroup K := A.subgroupOf K with hA'def
  have hmemQ : ∀ y : K, y ∈ (Q : Subgroup K) ↔ (y : G) ∈ S := fun y => by
    rw [hQ, mem_subgroupOf]
  have hA'Q : A' ≤ (Q : Subgroup K) := fun y hy => (hmemQ y).mpr (hAS (mem_subgroupOf.mp hy))
  have hA'wc : ∀ g : K, (∀ a ∈ A', g * a * g⁻¹ ∈ (Q : Subgroup K)) →
      ∀ a ∈ A', g * a * g⁻¹ ∈ A' := by
    intro g hg a ha
    have h1 := hwc g g.2 (fun b hb => by
      have := (hmemQ _).mp (hg ⟨b, hAK hb⟩ (mem_subgroupOf.mpr hb))
      simpa using this) a (mem_subgroupOf.mp ha)
    exact mem_subgroupOf.mpr (by simpa using h1)
  have hA'ab : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := fun a ha b hb =>
    Subtype.ext (hAab _ (mem_subgroupOf.mp ha) _ (mem_subgroupOf.mp hb))
  have hA'2 : ∀ a ∈ A', a ^ 2 = 1 := fun a ha =>
    Subtype.ext (by simpa using hA2 _ (mem_subgroupOf.mp ha))
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv
  rcases gold_cor4_self Q hA'Q hA'wc hA'ab hA'2 with hcl | ⟨-, hB⟩
  · left
    intro a ha g hg hga
    have h1 := hcl ⟨a, hAK ha⟩ (mem_subgroupOf.mpr ha) ⟨g, hg⟩ ((hmemQ _).mpr (by simpa using hga))
    simpa using mem_subgroupOf.mp h1
  · right
    intro x hxS hxA ⟨g, hgK, hgx⟩
    obtain ⟨B', hB'Q, hB'A, ⟨g', hg'⟩, hrel, hcard⟩ := hB ⟨x, hSK hxS⟩ ((hmemQ _).mpr hxS)
      (fun h => hxA (mem_subgroupOf.mp h)) ⟨⟨g, hgK⟩, mem_subgroupOf.mpr (by simpa using hgx)⟩
    set B : Subgroup G := B'.map K.subtype with hBdef
    have hBcard : Nat.card B = Nat.card B' := card_map_of_injective K.subtype_injective
    have hc₂ : Nat.card ((centralizer (A' : Set K)) ⊓ B' : Subgroup K) =
        Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) := by
      rw [← gmf_map_centralizer_inf hAK B', card_map_of_injective K.subtype_injective]
    have hc₁ : Nat.card ((centralizer ({(⟨x, hSK hxS⟩ : K)} : Set K)) ⊓ A' : Subgroup K) =
        Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) := by
      rw [← gmf_map_centralizer_singleton_inf hAK ⟨x, hSK hxS⟩,
        card_map_of_injective K.subtype_injective]
    have h₁ := relIndex_mul_card (H := centralizer ({(⟨x, hSK hxS⟩ : K)} : Set K)) (K := A')
    have h₂ := relIndex_mul_card (H := centralizer (A' : Set K)) (K := B')
    rw [hc₁, hA'card] at h₁
    rw [hc₂] at h₂
    refine ⟨B, ?_, ?_, ⟨g', g'.2, ?_⟩, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact (hmemQ b).mp (hB'Q hb)
    · intro hBA
      exact hB'A fun b hb => mem_subgroupOf.mpr (hBA ⟨b, hb, rfl⟩)
    · rintro _ ⟨b, hb, rfl⟩
      simpa using mem_subgroupOf.mp (hg' b hb)
    · rw [hBcard, ← h₁, ← h₂]
      calc _ = (centralizer ({(⟨x, hSK hxS⟩ : K)} : Set K)).relIndex A' *
            (Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) *
              Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G)) := by ring
        _ ≤ (centralizer (A' : Set K)).relIndex B' *
            (Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) *
              Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G)) :=
          Nat.mul_le_mul_right _ hrel
        _ = _ := by ring
    · rw [hBcard, ← hA'card]
      calc Nat.card A' * Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) ≤
            (Nat.card B' * (centralizer (A' : Set K)).relIndex B') *
              Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) :=
          Nat.mul_le_mul_right _ hcard
        _ = Nat.card B' * Nat.card B' := by rw [mul_assoc, h₂]

end CFSG.SeitzReduction.RankOne
