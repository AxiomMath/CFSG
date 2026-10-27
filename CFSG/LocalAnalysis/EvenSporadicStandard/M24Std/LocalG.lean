module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Local

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_mul_self_eq_of_mem
    (hL : IsSporadic L .M24) {u : G} (hu : u ∈ L)
    (hu2 : orderOf u = 2) : ∃ v ∈ L, v * v = u := by
  obtain ⟨v, hv⟩ := exists_mul_self_eq_of_orderOf_two hL (u := ⟨u, hu⟩)
    ((Subgroup.orderOf_coe (⟨u, hu⟩ : L)).symm.trans hu2)
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

theorem mem_of_mem_normalizer_sylow
    (hL : IsSporadic L .M24) {U : Subgroup G} (hUL : U ≤ L) (hUp : IsPGroup 2 U)
    (hUi : ¬ 2 ∣ (U.subgroupOf L).index) {g : G} (hg : g ∈ L)
    (hn : g ∈ normalizer (U : Set G)) : g ∈ U := by
  have hUp' : IsPGroup 2 (U.subgroupOf L) :=
    hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUL).symm
  have h := normalizer_eq_of_sylow hL hUp' hUi
  have hmem : (⟨g, hg⟩ : L) ∈ normalizer ((U.subgroupOf L : Subgroup L) : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hn x
  rw [h] at hmem
  exact hmem

omit [Finite G] in
theorem not_nine_dvd_card_centralizer_inf
    (hL : IsSporadic L .M24) {u : G} (hu : u ∈ L) (hu2 : orderOf u = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({u} : Set G) ⊓ L : Subgroup G) := by
  have h := not_nine_dvd_card_centralizer hL (u := (⟨u, hu⟩ : L))
    ((Subgroup.orderOf_coe (⟨u, hu⟩ : L)).symm.trans hu2)
  have hmap : (centralizer ({(⟨u, hu⟩ : L)} : Set L)).map L.subtype =
      centralizer ({u} : Set G) ⊓ L := by
    ext x
    simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, Subgroup.mem_inf,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨congrArg Subtype.val hy, y.2⟩
    · rintro ⟨hx, hxL⟩
      exact ⟨⟨x, hxL⟩, Subtype.ext hx, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective L.subtype_injective]
  exact h

omit [Finite G] in
theorem card_le_of_elemAbelian_le
    (hL : IsSporadic L .M24)
    {B : Subgroup G} (hBL : B ≤ L) (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hs : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 64 := by
  have h := card_le_of_elemAbelian hL (B.subgroupOf L) ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv] at h
    exact h
  · intro x hx y hy
    exact Subtype.ext (hc x hx y hy)
  · intro x hx
    exact Subtype.ext (hs x hx)

theorem nine_dvd_card_normalizer_inf
    (hL : IsSporadic L .M24) {A : Subgroup G} (hAL : A ≤ L)
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hs : ∀ x ∈ A, x * x = 1) (hA : Nat.card A = 64) :
    9 ∣ Nat.card (normalizer (A : Set G) ⊓ L : Subgroup G) := by
  have h := nine_dvd_card_normalizer hL (A := A.subgroupOf L) ?_ ?_ ?_
  · have hle : (normalizer ((A.subgroupOf L : Subgroup L) : Set L)).map L.subtype ≤
        normalizer (A : Set G) ⊓ L := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, x.2⟩
      show (x : G) ∈ normalizer (A : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      by_cases hy : y ∈ L
      · have := Subgroup.mem_normalizer_iff.1 hx ⟨y, hy⟩
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at this
        exact this
      · constructor
        · intro hyA
          exact absurd (hAL hyA) hy
        · intro hyA
          have h1 : (x : G) * y * (x : G)⁻¹ ∈ L := hAL hyA
          have h2 := L.mul_mem (L.mul_mem (L.inv_mem x.2) h1) x.2
          have e : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x = y := by group
          rw [e] at h2
          exact absurd h2 hy
    rw [← Subgroup.card_map_of_injective L.subtype_injective] at h
    exact h.trans (Subgroup.card_dvd_of_le hle)
  · intro x hx y hy
    exact Subtype.ext (hc x hx y hy)
  · intro x hx
    exact Subtype.ext (hs x hx)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
    exact hA

end CFSG.EvenSporadicStandard.M24Std
