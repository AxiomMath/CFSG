module

public import Mathlib.GroupTheory.PGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGeneric

public section

namespace CFSG.QuasithinUnique.Claim2526

open Equiv
open CFSG.QuasithinUnique.A6Facts

theorem commute_swap_apply {α : Type*} [DecidableEq α] {p : Equiv.Perm α} {a b : α} (hab : a ≠ b)
    (hc : p * Equiv.swap a b = Equiv.swap a b * p) :
    (p a = a ∨ p a = b) ∧ (p b = a ∨ p b = b) := by
  have key : ∀ x, p (Equiv.swap a b x) = Equiv.swap a b (p x) := by
    intro x
    have := congrArg (fun f => f x) hc
    simpa using this
  have hpa : p a = a ∨ p a = b := by
    by_cases h1 : p a = a
    · exact Or.inl h1
    · by_cases h2 : p a = b
      · exact Or.inr h2
      · exfalso
        have h3 : Equiv.swap a b (p a) = p a := Equiv.swap_apply_of_ne_of_ne h1 h2
        have h4 := key a
        rw [Equiv.swap_apply_left, h3] at h4
        exact hab (p.injective h4).symm
  refine ⟨hpa, ?_⟩
  have h4 := key a
  rw [Equiv.swap_apply_left] at h4
  rcases hpa with h | h
  · rw [h] at h4
    right
    rw [h4]
    exact Equiv.swap_apply_left a b
  · rw [h] at h4
    left
    rw [h4]
    exact Equiv.swap_apply_right a b

theorem perm_pow_four_of_commute_swap {p : Equiv.Perm (Fin 8)} {a b : Fin 8} (hab : a ≠ b)
    (hc : p * Equiv.swap a b = Equiv.swap a b * p) {m : ℕ} (hp : p ^ (2 ^ m) = 1) : p ^ 4 = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have hn2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have hn8 : n ≤ 8 := (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
    (by simpa using Finset.card_le_univ p.support)
  have hndvd : n ∣ 2 ^ m :=
    (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hp)
  obtain ⟨k, hk, hnk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hndvd
  have hk3 : k ≤ 3 := by
    by_contra hcon
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k
  · omega
  · rw [hnk]; norm_num
  · rw [hnk]; norm_num
  · exfalso
    rw [hnk] at hn
    obtain ⟨c, σ, hpc, hdisj, hcyc, hcard⟩ := Equiv.Perm.mem_cycleType_iff.mp hn
    have hsupp : c.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard]; simp
    have hσ : σ = 1 := by
      rw [← Equiv.Perm.support_eq_empty_iff]
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := Equiv.Perm.disjoint_iff_disjoint_support.mp hdisj
      rw [Finset.disjoint_left] at this
      exact this (by rw [hsupp]; exact Finset.mem_univ x) hx
    rw [hσ, mul_one] at hpc
    subst hpc
    have hpa : p a ≠ a := by
      have : a ∈ p.support := by rw [hsupp]; exact Finset.mem_univ a
      exact Equiv.Perm.mem_support.mp this
    have hpb : p b = Equiv.swap a b (p a) := by
      have := congrArg (fun f => f a) hc
      simpa using this
    have hpa' : p a = b := by
      by_contra hne
      have h1 : Equiv.swap a b (p a) = p a := Equiv.swap_apply_of_ne_of_ne hpa hne
      rw [h1] at hpb
      exact hab (p.injective hpb).symm
    have hpb' : p b = a := by rw [hpb, hpa']; simp
    have h2 : (p ^ 2) a = a := by
      rw [pow_two, Equiv.Perm.mul_apply, hpa', hpb']
    have h3 : p ^ 2 = 1 := (hcyc.pow_eq_one_iff).mpr ⟨a, hpa, h2⟩
    have h4 := hcyc.orderOf
    rw [hcard] at h4
    have h5 : orderOf p ∣ 2 := orderOf_dvd_of_pow_eq_one h3
    rw [h4] at h5
    omega

@[expose] def zeta8 : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7

theorem zeta8_mul_self : zeta8 * zeta8 = 1 := by decide

theorem zeta8_apply_apply (k : Fin 8) : zeta8 (zeta8 k) = k := by
  have := congrArg (fun f => f k) zeta8_mul_self
  simpa using this

@[expose] def B1 : Subgroup (Equiv.Perm (Fin 8)) := Subgroup.centralizer {zeta8}

theorem mem_B1_iff {σ : Equiv.Perm (Fin 8)} : σ ∈ B1 ↔ σ * zeta8 = zeta8 * σ := by
  unfold B1
  rw [Subgroup.mem_centralizer_singleton_iff]

theorem fin8_forall {P : Fin 8 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ k, P k := by
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

@[expose] def E8 : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | ∀ k, σ k = k ∨ σ k = zeta8 k}
  mul_mem' := by
    intro a b ha hb k
    rcases hb k with h | h
    · rw [Equiv.Perm.mul_apply, h]
      exact ha k
    · rw [Equiv.Perm.mul_apply, h]
      rcases ha (zeta8 k) with h' | h'
      · right; exact h'
      · left; rw [h', zeta8_apply_apply]
  one_mem' := fun k => Or.inl rfl
  inv_mem' := by
    intro a ha k
    have h := ha (a⁻¹ k)
    have h0 : a (a⁻¹ k) = k := by simp
    rw [h0] at h
    rcases h with h | h
    · left; exact h.symm
    · right
      calc a⁻¹ k = zeta8 (zeta8 (a⁻¹ k)) := (zeta8_apply_apply _).symm
        _ = zeta8 k := by rw [← h]

theorem zeta8_ne (k : Fin 8) : zeta8 k ≠ k := by
  revert k
  decide

theorem E8_sq {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ E8) : σ * σ = 1 := by
  ext k
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rcases hσ k with h | h
  · rw [h, h]
  · rw [h]
    rcases hσ (zeta8 k) with h' | h'
    · exfalso
      have : σ (zeta8 k) = σ k := by rw [h', h]
      exact zeta8_ne k (σ.injective this)
    · rw [h', zeta8_apply_apply]

theorem E8_normal {σ e : Equiv.Perm (Fin 8)} (hσ : σ ∈ B1) (he : e ∈ E8) : σ * e * σ⁻¹ ∈ E8 := by
  have hσ' := mem_B1_iff.mp hσ
  have hz : ∀ x, σ (zeta8 x) = zeta8 (σ x) := by
    intro x
    have := congrArg (fun f => f x) hσ'
    simpa using this
  intro k
  have h := he (σ⁻¹ k)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rcases h with h | h
  · left; rw [h]; simp
  · right
    rw [h, hz]
    simp

theorem swap01_mem_E8 : (Equiv.swap 0 1 : Equiv.Perm (Fin 8)) ∈ E8 := by
  intro k
  revert k
  decide

theorem swap23_mem_E8 : (Equiv.swap 2 3 : Equiv.Perm (Fin 8)) ∈ E8 := by
  intro k
  revert k
  decide

theorem swap45_mem_E8 : (Equiv.swap 4 5 : Equiv.Perm (Fin 8)) ∈ E8 := by
  intro k
  revert k
  decide

theorem swap67_mem_E8 : (Equiv.swap 6 7 : Equiv.Perm (Fin 8)) ∈ E8 := by
  intro k
  revert k
  decide

theorem centralizer_E8_le {σ : Equiv.Perm (Fin 8)}
    (h01 : σ * Equiv.swap 0 1 = Equiv.swap 0 1 * σ) (h23 : σ * Equiv.swap 2 3 = Equiv.swap 2 3 * σ)
    (h45 : σ * Equiv.swap 4 5 = Equiv.swap 4 5 * σ) (h67 : σ * Equiv.swap 6 7 = Equiv.swap 6 7 * σ) :
    σ ∈ E8 := by
  have a01 := commute_swap_apply (by decide) h01
  have a23 := commute_swap_apply (by decide) h23
  have a45 := commute_swap_apply (by decide) h45
  have a67 := commute_swap_apply (by decide) h67
  have z0 : zeta8 0 = 1 := by decide
  have z1 : zeta8 1 = 0 := by decide
  have z2 : zeta8 2 = 3 := by decide
  have z3 : zeta8 3 = 2 := by decide
  have z4 : zeta8 4 = 5 := by decide
  have z5 : zeta8 5 = 4 := by decide
  have z6 : zeta8 6 = 7 := by decide
  have z7 : zeta8 7 = 6 := by decide
  exact fin8_forall (by rw [z0]; exact a01.1) (by rw [z1]; exact Or.symm a01.2)
    (by rw [z2]; exact a23.1) (by rw [z3]; exact Or.symm a23.2)
    (by rw [z4]; exact a45.1) (by rw [z5]; exact Or.symm a45.2)
    (by rw [z6]; exact a67.1) (by rw [z7]; exact Or.symm a67.2)

@[expose] def p8GenC : List (List Nat) := [[1, 0, 2, 3, 4, 5, 6, 7], [2, 3, 0, 1, 4, 5, 6, 7], [4, 5, 6, 7, 0, 1, 2, 3]]

@[expose] def p8Tree : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 0), (2, 2), (3, 0), (3, 1), (4, 0), (4, 2), (5, 0), (5, 1), (6, 1), (6, 2), (7, 0), (7, 1), (8, 1), (8, 2), (9, 0), (9, 2), (10, 1), (10, 2), (11, 0), (11, 1), (12, 1), (12, 2), (13, 0), (13, 2), (14, 2), (15, 0), (15, 1), (16, 1), (16, 2), (17, 0), (17, 2), (18, 0), (18, 2), (20, 1), (20, 2), (22, 2), (23, 0), (23, 1), (24, 1), (24, 2), (25, 0), (25, 2), (26, 0), (26, 2), (28, 1), (28, 2), (30, 0), (30, 1), (31, 1), (31, 2), (32, 0), (32, 2), (33, 0), (33, 2), (35, 1), (35, 2), (37, 1), (37, 2), (39, 2), (41, 0), (41, 1), (42, 1), (42, 2), (43, 0), (43, 2), (44, 0), (44, 2), (46, 1), (46, 2), (48, 1), (48, 2), (50, 2), (52, 1), (52, 2), (53, 0), (53, 2), (54, 0), (54, 2), (56, 1), (56, 2), (58, 1), (58, 2), (60, 2), (62, 2), (65, 1), (65, 2), (66, 0), (66, 2), (67, 0), (67, 2), (69, 1), (69, 2), (71, 1), (71, 2), (73, 2), (75, 2), (78, 0), (78, 2), (80, 1), (80, 2), (82, 1), (82, 2), (84, 2), (86, 2), (90, 0), (90, 2), (92, 1), (92, 2), (94, 1), (94, 2), (96, 2), (98, 2), (102, 1), (102, 2), (104, 2), (106, 2), (110, 1), (110, 2), (112, 2), (114, 2), (118, 2), (122, 2)]

@[expose] def p8Tbl : List (List Nat) := [[1, 2, 3], [0, 4, 5], [6, 0, 7], [8, 9, 0], [10, 1, 11], [12, 13, 1], [2, 14, 15], [16, 17, 2], [3, 18, 19], [20, 3, 21], [4, 22, 23], [24, 25, 4], [5, 26, 27], [28, 5, 29], [22, 6, 30], [31, 32, 6], [7, 33, 34], [35, 7, 36], [37, 8, 38], [27, 34, 8], [9, 39, 40], [29, 36, 9], [14, 10, 41], [42, 43, 10], [11, 44, 45], [46, 11, 47], [48, 12, 49], [19, 45, 12], [13, 50, 51], [21, 47, 13], [52, 53, 14], [15, 54, 55], [56, 15, 57], [58, 16, 59], [55, 19, 16], [17, 60, 61], [57, 21, 17], [18, 62, 63], [49, 59, 18], [62, 20, 64], [51, 61, 20], [65, 66, 22], [23, 67, 68], [69, 23, 70], [71, 24, 72], [68, 27, 24], [25, 73, 74], [70, 29, 25], [26, 75, 76], [38, 72, 26], [75, 28, 77], [40, 74, 28], [30, 78, 79], [80, 30, 81], [82, 31, 83], [34, 79, 31], [32, 84, 85], [36, 81, 32], [33, 86, 87], [83, 38, 33], [86, 35, 88], [85, 40, 35], [39, 37, 89], [76, 87, 37], [77, 88, 39], [41, 90, 91], [92, 41, 93], [94, 42, 95], [45, 91, 42], [43, 96, 97], [47, 93, 43], [44, 98, 99], [95, 49, 44], [98, 46, 100], [97, 51, 46], [50, 48, 101], [63, 99, 48], [64, 100, 50], [102, 52, 103], [91, 55, 52], [53, 104, 105], [93, 57, 53], [54, 106, 107], [59, 103, 54], [106, 56, 108], [61, 105, 56], [60, 58, 109], [107, 63, 58], [108, 64, 60], [101, 109, 62], [110, 65, 111], [79, 68, 65], [66, 112, 113], [81, 70, 66], [67, 114, 115], [72, 111, 67], [114, 69, 116], [74, 113, 69], [73, 71, 117], [115, 76, 71], [116, 77, 73], [89, 117, 75], [78, 118, 119], [111, 83, 78], [118, 80, 120], [113, 85, 80], [84, 82, 121], [87, 119, 82], [88, 120, 84], [121, 89, 86], [90, 122, 123], [103, 95, 90], [122, 92, 124], [105, 97, 92], [96, 94, 125], [99, 123, 94], [100, 124, 96], [125, 101, 98], [104, 102, 126], [123, 107, 102], [124, 108, 104], [109, 126, 106], [112, 110, 127], [119, 115, 110], [120, 116, 112], [117, 127, 114], [127, 121, 118], [126, 125, 122]]

theorem p8_tbl : Core.tblCheckC (List.range 8) p8GenC
    (Core.buildCodes (List.range 8) p8GenC p8Tree) p8Tbl = true := by decide +kernel

theorem p8_nodup : (Core.buildCodes (List.range 8) p8GenC p8Tree).Nodup := by decide +kernel

theorem p8_length : (Core.buildCodes (List.range 8) p8GenC p8Tree).length = 128 := by
  decide +kernel

@[expose] def p8Gens : List (Equiv.Perm (Fin 8)) :=
  [Equiv.swap 0 1, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7]

theorem p8Gens_code : p8Gens.map (codeN 8) = p8GenC := by decide +kernel

@[expose] def P8 : Subgroup (Equiv.Perm (Fin 8)) := Subgroup.closure {g | g ∈ p8Gens}

theorem card_P8 : Nat.card P8 = 128 := by
  have := card_closure_eq_of_tblN p8Gens_code p8_tbl p8_nodup
  rw [p8_length] at this
  exact this

theorem isPGroup_P8 : IsPGroup 2 P8 := IsPGroup.of_card (n := 7) (by rw [card_P8]; norm_num)

theorem P8_le_B1 : P8 ≤ B1 := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [p8Gens, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact mem_B1_iff.mpr (by decide)
  · exact mem_B1_iff.mpr (by decide)
  · exact mem_B1_iff.mpr (by decide)

theorem swap01_mem_B1 : (Equiv.swap 0 1 : Equiv.Perm (Fin 8)) ∈ B1 :=
  mem_B1_iff.mpr (by decide)

theorem card_perm_fin8 : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem exists_perm_conj_swap {c d : Fin 8} (hcd : c ≠ d) :
    ∃ ρ : Equiv.Perm (Fin 8), ρ * Equiv.swap 0 1 * ρ⁻¹ = Equiv.swap c d := by
  have := Equiv.Perm.isConj_swap (by decide : (0 : Fin 8) ≠ 1) hcd
  exact isConj_iff.mp this

theorem eq_top_of_swaps {X : Subgroup (Equiv.Perm (Fin 8))}
    (h : ∀ c d : Fin 8, c ≠ d → Equiv.swap c d ∈ X) : X = ⊤ := by
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap]
  apply (Subgroup.closure_le _).mpr
  rintro σ ⟨c, d, hcd, rfl⟩
  exact h c d hcd

@[expose] def v8GenC : List (List Nat) := [[1, 0, 3, 2, 4, 5, 6, 7], [2, 3, 0, 1, 4, 5, 6, 7], [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 2, 3, 6, 7, 4, 5]]

@[expose] def v8Tree : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3), (5, 2), (5, 3), (6, 3), (8, 3), (11, 3)]

@[expose] def v8Tbl : List (List Nat) := [[1, 2, 3, 4], [0, 5, 6, 7], [5, 0, 8, 9], [6, 8, 0, 10], [7, 9, 10, 0], [2, 1, 11, 12], [3, 11, 1, 13], [4, 12, 13, 1], [11, 3, 2, 14], [12, 4, 14, 2], [13, 14, 4, 3], [8, 6, 5, 15], [9, 7, 15, 5], [10, 15, 7, 6], [15, 10, 9, 8], [14, 13, 12, 11]]

theorem v8_tbl : Core.tblCheckC (List.range 8) v8GenC
    (Core.buildCodes (List.range 8) v8GenC v8Tree) v8Tbl = true := by decide +kernel

theorem v8_nodup : (Core.buildCodes (List.range 8) v8GenC v8Tree).Nodup := by decide +kernel

@[expose] def v8g1 : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def v8g2 : Equiv.Perm (Fin 8) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def v8g3 : Equiv.Perm (Fin 8) := Equiv.swap 4 5 * Equiv.swap 6 7

@[expose] def v8g4 : Equiv.Perm (Fin 8) := Equiv.swap 4 6 * Equiv.swap 5 7

@[expose] def v8Gens : List (Equiv.Perm (Fin 8)) := [v8g1, v8g2, v8g3, v8g4]

theorem v8Gens_code : v8Gens.map (codeN 8) = v8GenC := by decide +kernel

@[expose] def V8 : Subgroup (Equiv.Perm (Fin 8)) := Subgroup.closure {g | g ∈ v8Gens}

@[expose] def v8Codes : List (List Nat) := Core.buildCodes (List.range 8) v8GenC v8Tree

theorem mem_V8_iff {x : Equiv.Perm (Fin 8)} : x ∈ V8 ↔ codeN 8 x ∈ v8Codes :=
  (mem_closure_iff_of_tblN v8Gens_code v8_tbl).1 x

theorem exists_V8_of_code {c : List Nat} (hc : c ∈ v8Codes) :
    ∃ x ∈ V8, codeN 8 x = c :=
  (mem_closure_iff_of_tblN v8Gens_code v8_tbl).2 c hc

theorem V8_sq {x : Equiv.Perm (Fin 8)} (hx : x ∈ V8) : x * x = 1 := by
  have h : ∀ c ∈ v8Codes, Core.cmul c c = List.range 8 := by decide +kernel
  apply codeN_injective (n := 8)
  rw [codeN_mul, codeN_one]
  exact h _ (mem_V8_iff.mp hx)

theorem mem_normalizer_of_forall_conj {H : Type*} [Group H] [Finite H] {E : Subgroup H} {g : H}
    (h : ∀ y ∈ E, g * y * g⁻¹ ∈ E) : g ∈ Subgroup.normalizer (E : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  let φ : ↥E → ↥E := fun z => ⟨g * z * g⁻¹, h z z.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : g * (a : H) * g⁻¹ = g * (b : H) * g⁻¹ := congrArg Subtype.val hab
    apply Subtype.ext
    simpa using h1
  obtain ⟨z, hz⟩ := Finite.injective_iff_surjective.mp hinj ⟨g * y * g⁻¹, hy⟩
  have h1 : g * (z : H) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hz
  have : (z : H) = y := by simpa using h1
  rw [← this]
  exact z.2

@[expose] def B2 : Subgroup (Equiv.Perm (Fin 8)) := Subgroup.normalizer (V8 : Set (Equiv.Perm (Fin 8)))

theorem mem_B2_of_codes {g : Equiv.Perm (Fin 8)}
    (h : ∀ c ∈ v8Codes, ∃ c' ∈ v8Codes, Core.cmul (codeN 8 g) c = Core.cmul c' (codeN 8 g)) :
    g ∈ B2 := by
  apply mem_normalizer_of_forall_conj
  intro y hy
  obtain ⟨c', hc', hcc⟩ := h _ (mem_V8_iff.mp hy)
  obtain ⟨y', hy', rfl⟩ := exists_V8_of_code hc'
  have : g * y = y' * g := by
    apply codeN_injective (n := 8)
    rw [codeN_mul, codeN_mul]
    exact hcc
  have e : g * y * g⁻¹ = y' := by rw [this]; group
  rw [e]
  exact hy'

theorem swap12_mem_B2 : (Equiv.swap 1 2 : Equiv.Perm (Fin 8)) ∈ B2 := by
  apply mem_B2_of_codes
  decide +kernel

theorem P8_le_B2 : P8 ≤ B2 := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [p8Gens, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact mem_B2_of_codes (by decide +kernel)
  · exact mem_B2_of_codes (by decide +kernel)
  · exact mem_B2_of_codes (by decide +kernel)

theorem codeN8 (σ : Equiv.Perm (Fin 8)) :
    codeN 8 σ = [(σ 0 : ℕ), (σ 1 : ℕ), (σ 2 : ℕ), (σ 3 : ℕ), (σ 4 : ℕ), (σ 5 : ℕ), (σ 6 : ℕ),
      (σ 7 : ℕ)] := by
  unfold codeN
  simp only [List.ofFn_succ, List.ofFn_zero]
  rfl

@[expose] def v8List (u v : Fin 8) : List Nat :=
  [(u : ℕ), (v8g1 u : ℕ), (v8g2 u : ℕ), (v8g1 (v8g2 u) : ℕ), (v : ℕ), (v8g3 v : ℕ), (v8g4 v : ℕ),
    (v8g3 (v8g4 v) : ℕ)]

theorem v8List_mem : ∀ u v : Fin 8, (v8List u v).Nodup → v8List u v ∈ v8Codes := by
  decide +kernel

theorem centralizer_V8_le {σ : Equiv.Perm (Fin 8)} (h1 : σ * v8g1 = v8g1 * σ)
    (h2 : σ * v8g2 = v8g2 * σ) (h3 : σ * v8g3 = v8g3 * σ) (h4 : σ * v8g4 = v8g4 * σ) :
    σ ∈ V8 := by
  rw [mem_V8_iff]
  have key : ∀ (g : Equiv.Perm (Fin 8)) (x : Fin 8), σ * g = g * σ → σ (g x) = g (σ x) := by
    intro g x h
    have := congrArg (fun f => f x) h
    simpa using this
  have e1 : σ 1 = v8g1 (σ 0) := by
    have := key _ 0 h1
    have h0 : v8g1 0 = 1 := by decide
    rw [h0] at this
    exact this
  have e2 : σ 2 = v8g2 (σ 0) := by
    have := key _ 0 h2
    have h0 : v8g2 0 = 2 := by decide
    rw [h0] at this
    exact this
  have e3 : σ 3 = v8g1 (v8g2 (σ 0)) := by
    have := key _ 2 h1
    have h0 : v8g1 2 = 3 := by decide
    rw [h0, e2] at this
    exact this
  have e5 : σ 5 = v8g3 (σ 4) := by
    have := key _ 4 h3
    have h0 : v8g3 4 = 5 := by decide
    rw [h0] at this
    exact this
  have e6 : σ 6 = v8g4 (σ 4) := by
    have := key _ 4 h4
    have h0 : v8g4 4 = 6 := by decide
    rw [h0] at this
    exact this
  have e7 : σ 7 = v8g3 (v8g4 (σ 4)) := by
    have := key _ 6 h3
    have h0 : v8g3 6 = 7 := by decide
    rw [h0, e6] at this
    exact this
  have hcode : codeN 8 σ = v8List (σ 0) (σ 4) := by
    rw [codeN8, e1, e2, e3, e5, e6, e7]
    rfl
  have hnd : (codeN 8 σ).Nodup := by
    unfold codeN
    rw [List.nodup_ofFn]
    intro a b h
    exact σ.injective (Fin.ext h)
  rw [hcode] at hnd ⊢
  exact v8List_mem _ _ hnd

theorem sup_B1_B2 : B1 ⊔ B2 = ⊤ := by
  have s01 : (Equiv.swap 0 1 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 := Subgroup.mem_sup_left swap01_mem_B1
  have s12 : (Equiv.swap 1 2 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 := Subgroup.mem_sup_right swap12_mem_B2
  have s23 : (Equiv.swap 2 3 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 :=
    Subgroup.mem_sup_left (mem_B1_iff.mpr (by decide))
  have c24 : (Equiv.swap 2 4 * Equiv.swap 3 5 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 :=
    Subgroup.mem_sup_left (mem_B1_iff.mpr (by decide))
  have s45 : (Equiv.swap 4 5 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 :=
    Subgroup.mem_sup_left (mem_B1_iff.mpr (by decide))
  have c46 : (Equiv.swap 4 6 * Equiv.swap 5 7 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 :=
    Subgroup.mem_sup_left (mem_B1_iff.mpr (by decide))
  have s67 : (Equiv.swap 6 7 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 :=
    Subgroup.mem_sup_left (mem_B1_iff.mpr (by decide))
  have conj : ∀ (a b : Equiv.Perm (Fin 8)), a ∈ B1 ⊔ B2 → b ∈ B1 ⊔ B2 → a * b * a⁻¹ ∈ B1 ⊔ B2 :=
    fun a b ha hb => Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha)
  have h10 : (Equiv.swap 1 0 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 := by
    rw [Equiv.swap_comm]; exact s01
  have h12 := s12
  have h13 : (Equiv.swap 1 3 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 := by
    have e : (Equiv.swap 1 3 : Equiv.Perm (Fin 8)) = Equiv.swap 2 3 * Equiv.swap 1 2 * (Equiv.swap 2 3)⁻¹ := by
      decide
    rw [e]; exact conj _ _ s23 s12
  have h14 : (Equiv.swap 1 4 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 := by
    have e : (Equiv.swap 1 4 : Equiv.Perm (Fin 8)) =
        (Equiv.swap 2 4 * Equiv.swap 3 5) * Equiv.swap 1 2 * (Equiv.swap 2 4 * Equiv.swap 3 5)⁻¹ := by
      decide
    rw [e]; exact conj _ _ c24 s12
  have h15 : (Equiv.swap 1 5 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 := by
    have e : (Equiv.swap 1 5 : Equiv.Perm (Fin 8)) = Equiv.swap 4 5 * Equiv.swap 1 4 * (Equiv.swap 4 5)⁻¹ := by
      decide
    rw [e]; exact conj _ _ s45 h14
  have h16 : (Equiv.swap 1 6 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 := by
    have e : (Equiv.swap 1 6 : Equiv.Perm (Fin 8)) =
        (Equiv.swap 4 6 * Equiv.swap 5 7) * Equiv.swap 1 4 * (Equiv.swap 4 6 * Equiv.swap 5 7)⁻¹ := by
      decide
    rw [e]; exact conj _ _ c46 h14
  have h17 : (Equiv.swap 1 7 : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 := by
    have e : (Equiv.swap 1 7 : Equiv.Perm (Fin 8)) = Equiv.swap 6 7 * Equiv.swap 1 6 * (Equiv.swap 6 7)⁻¹ := by
      decide
    rw [e]; exact conj _ _ s67 h16
  have h1 : ∀ k : Fin 8, k ≠ 1 → (Equiv.swap 1 k : Equiv.Perm (Fin 8)) ∈ B1 ⊔ B2 := by
    intro k hk
    fin_cases k
    · exact h10
    · exact absurd rfl hk
    · exact h12
    · exact h13
    · exact h14
    · exact h15
    · exact h16
    · exact h17
  apply eq_top_of_swaps
  intro c d hcd
  by_cases hc : c = 1
  · rw [hc]; exact h1 d (fun h => hcd (hc.trans h.symm))
  · by_cases hd : d = 1
    · rw [hd, Equiv.swap_comm]; exact h1 c hc
    · have e : (Equiv.swap c d : Equiv.Perm (Fin 8)) =
          Equiv.swap 1 c * Equiv.swap 1 d * (Equiv.swap 1 c)⁻¹ := by
        revert c d
        decide
      rw [e]
      exact conj _ _ (h1 c hc) (h1 d hd)

end CFSG.QuasithinUnique.Claim2526
