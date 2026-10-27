module

public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.EvenSmallLie.OmegaEight.Cover

open Subgroup

variable {U : Type*} [Group U]

theorem normal_of_le_center {K : Subgroup U} (hK : K ≤ center U) : K.Normal :=
  ⟨fun k hk g => by rwa [(mem_center_iff.1 (hK hk) g), mul_inv_cancel_right]⟩

theorem sq_mem_of_card_eq {M L : Subgroup U} [Finite M] (hL : L ≤ M)
    (hLc : Nat.card M = 2 * Nat.card L) {m : U} (hm : m ∈ M) : m ^ 2 ∈ L := by
  have hi : (L.subgroupOf M).index = 2 := by
    have h1 := (L.subgroupOf M).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hL).toEquiv, hLc] at h1
    have hpos : 0 < Nat.card L := Nat.card_pos_iff.2 ⟨⟨1, L.one_mem⟩, Finite.of_injective
      (fun x : L => (⟨x, hL x.2⟩ : M)) fun x y h => Subtype.ext (congrArg Subtype.val h :)⟩
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])
  have := sq_mem_of_index_two hi ⟨m, hm⟩
  rw [mem_subgroupOf] at this
  simpa using this

theorem eq_of_sq_ne_one {M K K' : Subgroup U} [Finite M] (hM4 : Nat.card M ≤ 4) (hK : K ≤ M)
    (hK' : K' ≤ M) (hKc : Nat.card M = 2 * Nat.card K) (hK'c : Nat.card M = 2 * Nat.card K')
    {m : U} (hm : m ∈ M) (hm2 : m ^ 2 ≠ 1) : K = K' := by
  have hfin : ∀ {L : Subgroup U}, L ≤ M → Finite L := fun hL =>
    Finite.of_injective (fun x => (⟨x, hL x.2⟩ : M)) fun x y h =>
      Subtype.ext (congrArg Subtype.val h :)
  have : Finite K := hfin hK
  have : Finite K' := hfin hK'
  have hmK := sq_mem_of_card_eq hK hKc hm
  have hmK' := sq_mem_of_card_eq hK' hK'c hm
  have hne : K ⊓ K' ≠ ⊥ := fun h => hm2 (by
    have : m ^ 2 ∈ K ⊓ K' := ⟨hmK, hmK'⟩
    rwa [h, mem_bot] at this)
  have hfi : Finite (K ⊓ K' : Subgroup U) := hfin (inf_le_left.trans hK)
  have h2 : 2 ≤ Nat.card (K ⊓ K' : Subgroup U) := (one_lt_card_iff_ne_bot _).2 hne
  have h1 : K ⊓ K' = K := eq_of_le_of_card_ge inf_le_left (by omega)
  have h1' : K ⊓ K' = K' := eq_of_le_of_card_ge inf_le_right (by omega)
  rw [← h1, h1']

theorem length_le_card {M : Subgroup U} [Finite M] {l : List U} (hl : l.Nodup)
    (hM : ∀ g ∈ l, g ∈ M) : l.length ≤ Nat.card M := by
  classical
  have : Fintype M := Fintype.ofFinite M
  rw [Nat.card_eq_fintype_card]
  have hl' : (l.pmap (fun g hg => (⟨g, hg⟩ : M)) hM).Nodup :=
    hl.pmap fun _ _ _ _ h => congrArg Subtype.val h
  calc l.length = (l.pmap (fun g hg => (⟨g, hg⟩ : M)) hM).length := (List.length_pmap ..).symm
    _ = (l.pmap (fun g hg => (⟨g, hg⟩ : M)) hM).toFinset.card :=
      (List.toFinset_card_of_nodup hl').symm
    _ ≤ Fintype.card M := Finset.card_le_univ _

theorem mem_of_exponent_two {M : Subgroup U} [Finite M] (hMc : M ≤ center U)
    (hM4 : Nat.card M ≤ 4) (τ : U ≃* U) (hτ3 : ∀ u, τ (τ (τ u)) = u)
    (hτM : ∀ m ∈ M, τ m ∈ M) {R : Type*} [Group R] (ρ : U →* R) {x y : U} (hx : x ^ 2 ∈ M)
    (hxy : y⁻¹ * τ x ∈ M) (hρx : ρ x ^ 2 = 1) (hρy : ρ y ^ 2 ≠ 1)
    (h2 : ∀ m ∈ M, m ^ 2 = 1) :
    [1, x ^ 2, τ (x ^ 2), τ (τ (x ^ 2))].Nodup ∧
      ∀ m ∈ M, m = 1 ∨ m = x ^ 2 ∨ m = τ (x ^ 2) ∨ m = τ (τ (x ^ 2)) := by
  have hm₀ : y⁻¹ * τ x ∈ center U := hMc hxy
  have hz₂ : τ (x ^ 2) = y ^ 2 := by
    have hc : Commute y (y⁻¹ * τ x) := mem_center_iff.1 hm₀ y
    rw [map_pow, show τ x = y * (y⁻¹ * τ x) by rw [mul_inv_cancel_left], hc.mul_pow,
      h2 _ hxy, mul_one]
  have hz₁N : ρ (x ^ 2) = 1 := by rw [map_pow, hρx]
  have hz₂N : ρ (τ (x ^ 2)) ≠ 1 := by rwa [hz₂, map_pow]
  have h12 : x ^ 2 ≠ τ (x ^ 2) := fun h => hz₂N (by rw [← h, hz₁N])
  have h01 : (1 : U) ≠ x ^ 2 := fun h => h12 (by rw [← h, map_one])
  have h02 : (1 : U) ≠ τ (x ^ 2) := fun h => hz₂N (by rw [← h, map_one])
  have h03 : (1 : U) ≠ τ (τ (x ^ 2)) := fun h => h02 (τ.injective (by rw [← h, map_one]))
  have h23 : τ (x ^ 2) ≠ τ (τ (x ^ 2)) := fun h => h12 (τ.injective h)
  have h13 : x ^ 2 ≠ τ (τ (x ^ 2)) := fun h => h12 (by
    have := congrArg τ h
    rwa [hτ3, eq_comm] at this)
  have hnd : [1, x ^ 2, τ (x ^ 2), τ (τ (x ^ 2))].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_or, and_true, not_false_eq_true]
    exact ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23⟩
  refine ⟨hnd, fun m hm => ?_⟩
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hm1, hm2, hm3, hm4⟩ := hne
  have hnd' : [m, 1, x ^ 2, τ (x ^ 2), τ (τ (x ^ 2))].Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, hnd⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hm1, hm2, hm3, hm4⟩
  have hmem : ∀ g ∈ [m, 1, x ^ 2, τ (x ^ 2), τ (τ (x ^ 2))], g ∈ M := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl)
    · exact hm
    · exact M.one_mem
    · exact hx
    · exact hτM _ hx
    · exact hτM _ (hτM _ hx)
  have := length_le_card hnd' hmem
  simp only [List.length_cons, List.length_nil] at this
  omega

theorem exists_map_eq_zpowers {M : Subgroup U} [Finite M] (hMc : M ≤ center U)
    (hM4 : Nat.card M ≤ 4) (τ : U ≃* U) (hτ3 : ∀ u, τ (τ (τ u)) = u)
    (hτM : ∀ m ∈ M, τ m ∈ M) {R : Type*} [Group R] (ρ : U →* R) {x y : U} (hx : x ^ 2 ∈ M)
    (hxy : y⁻¹ * τ x ∈ M) (hρx : ρ x ^ 2 = 1) (hρy : ρ y ^ 2 ≠ 1)
    (h2 : ∀ m ∈ M, m ^ 2 = 1) {K : Subgroup U} (hK : K ≤ M) (hKc : Nat.card M = 2 * Nat.card K) :
    ∃ e : U ≃* U, K.map (e : U →* U) = zpowers (x ^ 2) := by
  obtain ⟨hnd, hall⟩ := mem_of_exponent_two hMc hM4 τ hτ3 hτM ρ hx hxy hρx hρy h2
  have h4 : 4 ≤ Nat.card M := by
    have := length_le_card hnd (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro g (rfl | rfl | rfl | rfl)
      · exact M.one_mem
      · exact hx
      · exact hτM _ hx
      · exact hτM _ (hτM _ hx))
    simpa using this
  have hK2 : Nat.card K = 2 := by omega
  obtain ⟨⟨k, hk⟩, hk1⟩ := (ne_bot_iff_exists_ne_one (H := K)).1 (by
    rintro rfl
    rw [card_bot] at hK2
    omega)
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hKk : zpowers k = K := by
    have : Finite K := Nat.finite_of_card_ne_zero (by omega)
    refine eq_of_le_of_card_ge (zpowers_le.2 hk) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (h2 k (hK hk)) hk1', hK2]
  rcases hall k (hK hk) with h | h | h | h
  · exact absurd h hk1'
  · refine ⟨MulEquiv.refl U, ?_⟩
    rw [← hKk, MonoidHom.map_zpowers, h]
    rfl
  · refine ⟨τ.trans τ, ?_⟩
    rw [← hKk, MonoidHom.map_zpowers, h]
    exact congrArg zpowers (hτ3 _)
  · refine ⟨τ, ?_⟩
    rw [← hKk, MonoidHom.map_zpowers, h]
    exact congrArg zpowers (hτ3 _)

theorem nonempty_quotient_mulEquiv {M : Subgroup U} [Finite M] (hMc : M ≤ center U)
    (hM4 : Nat.card M ≤ 4) (τ : U ≃* U) (hτ3 : ∀ u, τ (τ (τ u)) = u)
    (hτM : ∀ m ∈ M, τ m ∈ M) {R : Type*} [Group R] (ρ : U →* R) {x y : U} (hx : x ^ 2 ∈ M)
    (hxy : y⁻¹ * τ x ∈ M) (hρx : ρ x ^ 2 = 1) (hρy : ρ y ^ 2 ≠ 1) {K K' : Subgroup U}
    [K.Normal] [K'.Normal] (hK : K ≤ M) (hK' : K' ≤ M) (hKc : Nat.card M = 2 * Nat.card K)
    (hK'c : Nat.card M = 2 * Nat.card K') : Nonempty (U ⧸ K ≃* U ⧸ K') := by
  by_cases h2 : ∀ m ∈ M, m ^ 2 = 1
  · have : (zpowers (x ^ 2)).Normal := normal_of_le_center ((zpowers_le.2 hx).trans hMc)
    obtain ⟨e, he⟩ := exists_map_eq_zpowers hMc hM4 τ hτ3 hτM ρ hx hxy hρx hρy h2 hK hKc
    obtain ⟨e', he'⟩ := exists_map_eq_zpowers hMc hM4 τ hτ3 hτM ρ hx hxy hρx hρy h2 hK' hK'c
    exact ⟨(QuotientGroup.congr K _ e he).trans (QuotientGroup.congr K' _ e' he').symm⟩
  · obtain ⟨m, hm⟩ := not_forall.1 h2
    obtain ⟨hmM, hm2⟩ := not_imp.1 hm
    exact ⟨QuotientGroup.quotientMulEquivOfEq (eq_of_sq_ne_one hM4 hK hK' hKc hK'c hmM hm2)⟩

end CFSG.EvenSmallLie.OmegaEight.Cover
