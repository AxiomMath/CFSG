module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

open scoped Pointwise

theorem pow_three_mem_of_relIndex_eq_seven {E : Type*} [Group E] [Finite E] {T : Subgroup E}
    (h7 : T.relIndex (normalizer (T : Set E)) = 7) {y : E} (hy : y ∈ normalizer (T : Set E))
    (hy3 : y ^ 3 = 1) : y ∈ T := by
  set N := normalizer (T : Set E)
  have hpow : (⟨y, hy⟩ : N) ^ (T.subgroupOf N).index ∈ T.subgroupOf N :=
    Subgroup.pow_index_mem (T.subgroupOf N) ⟨y, hy⟩
  have hidx : (T.subgroupOf N).index = 7 := h7
  have hpow' : y ^ 7 ∈ T := by
    simpa only [hidx, Subgroup.mem_subgroupOf, SubmonoidClass.coe_pow,
      Subtype.coe_mk] using hpow
  have h7eq : y ^ 7 = y := by
    rw [show (7 : ℕ) = 3 + 3 + 1 by norm_num, pow_add, pow_add, hy3]
    simp
  rwa [h7eq] at hpow'

theorem exists_conj_centralizer_of_involution {E : Type*} [Group E] [Finite E] (P : Sylow 2 E)
    {t : E} (hCt : centralizer ({t} : Set E) = (P : Subgroup E))
    (hconjT : ∀ y ∈ (P : Subgroup E), y ≠ 1 →
      ∃ n ∈ normalizer ((P : Subgroup E) : Set E), n * t * n⁻¹ = y)
    {u : E} (hu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ g : E, ∀ y : E, y * u = u * y ↔ g⁻¹ * y * g ∈ (P : Subgroup E) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf u = 2 := orderOf_eq_prime (by simpa [pow_two] using hu) hu1
  have hcard : Nat.card (zpowers u) = 2 ^ (1 : ℕ) := by
    rw [Nat.card_zpowers, hord]; norm_num
  have hPgrp : IsPGroup 2 (zpowers u) := IsPGroup.of_card hcard
  obtain ⟨Q, hQ⟩ := hPgrp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E P Q
  have huQ : u ∈ Q := hQ (mem_zpowers u)
  have hyP : g⁻¹ * u * g ∈ (P : Subgroup E) := by
    have h1 : u ∈ (↑(g • P) : Set E) := by rw [hg]; exact huQ
    rw [Sylow.coe_smul] at h1
    have h := (Set.mem_smul_set_iff_inv_smul_mem.mp h1)
    rw [MulAut.smul_def, MulAut.conj_inv_apply] at h
    exact h
  have hy1 : g⁻¹ * u * g ≠ 1 := by
    intro h
    apply hu1
    have key : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    rw [h] at key
    simpa using key.symm
  obtain ⟨n, hnN, hn⟩ := hconjT (g⁻¹ * u * g) hyP hy1
  refine ⟨g * n, fun y => ?_⟩
  have hgt : (g * n) * t * (g * n)⁻¹ = u := by
    calc (g * n) * t * (g * n)⁻¹ = g * (n * t * n⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * u * g) * g⁻¹ := by rw [hn]
      _ = u := by group
  have hiff : y * u = u * y ↔ ((g * n)⁻¹ * y * (g * n)) * t =
      t * ((g * n)⁻¹ * y * (g * n)) := by
    constructor
    · intro h
      have h1 : (g * n)⁻¹ * (y * u) * (g * n) =
          ((g * n)⁻¹ * y * (g * n)) * t := by rw [← hgt]; group
      have h2 : (g * n)⁻¹ * (u * y) * (g * n) =
          t * ((g * n)⁻¹ * y * (g * n)) := by rw [← hgt]; group
      rw [h] at h1
      rw [← h1, h2]
    · intro h
      have h1 : (g * n) * (((g * n)⁻¹ * y * (g * n)) * t) * (g * n)⁻¹ =
          y * u := by rw [← hgt]; group
      have h2 : (g * n) * (t * ((g * n)⁻¹ * y * (g * n))) * (g * n)⁻¹ =
          u * y := by rw [← hgt]; group
      rw [h] at h1
      rw [← h1, h2]
  rw [hiff, ← hCt, Subgroup.mem_centralizer_singleton_iff]

theorem false_of_conj_centralizers {E : Type*} [Group E] [Finite E] {T : Subgroup E}
    (hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hT : Nat.card T = 8)
    (hN3 : ∀ y ∈ normalizer (T : Set E), y ^ 3 = 1 → y ∈ T)
    (hconj : ∀ u : E, u * u = 1 → u ≠ 1 →
      ∃ g : E, ∀ y : E, y * u = u * y ↔ g⁻¹ * y * g ∈ T)
    {a x : E} (ha : a * a = 1) (ha1 : a ≠ 1) (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hcomm : (x * a * x⁻¹) * a = a * (x * a * x⁻¹)) : False := by
  have hcc : (x * a * x⁻¹) * (x * a * x⁻¹) = 1 := by
    have h2 : (x * a * x⁻¹) * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
    rw [h2, ha]; group
  have hc1 : x * a * x⁻¹ ≠ 1 := by
    intro h
    apply ha1
    have key : x⁻¹ * (x * a * x⁻¹) * x = a := by group
    rw [h] at key
    simpa using key.symm
  obtain ⟨ga, hga⟩ := hconj a ha ha1
  have hAga : ∀ y, y ∈ centralizer ({a} : Set E) ↔ ga⁻¹ * y * ga ∈ T := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hga y
  obtain ⟨gc, hgc⟩ := hconj (x * a * x⁻¹) hcc hc1
  have hBgc : ∀ y, y ∈ centralizer ({x * a * x⁻¹} : Set E) ↔ gc⁻¹ * y * gc ∈ T := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hgc y
  have hAcomm : ∀ y ∈ centralizer ({a} : Set E),
      ∀ y' ∈ centralizer ({a} : Set E), y * y' = y' * y := by
    intro y hy y' hy'
    have hyT : ga⁻¹ * y * ga ∈ T := (hAga y).mp hy
    have hy'T : ga⁻¹ * y' * ga ∈ T := (hAga y').mp hy'
    have hcommT : (ga⁻¹ * y * ga) * (ga⁻¹ * y' * ga) =
        (ga⁻¹ * y' * ga) * (ga⁻¹ * y * ga) := hab _ hyT _ hy'T
    have h1 : ga * ((ga⁻¹ * y * ga) * (ga⁻¹ * y' * ga)) * ga⁻¹ = y * y' := by group
    have h2 : ga * ((ga⁻¹ * y' * ga) * (ga⁻¹ * y * ga)) * ga⁻¹ = y' * y := by group
    rw [← h1, hcommT, h2]
  have hBcomm : ∀ y ∈ centralizer ({x * a * x⁻¹} : Set E),
      ∀ y' ∈ centralizer ({x * a * x⁻¹} : Set E), y * y' = y' * y := by
    intro y hy y' hy'
    have hyT : gc⁻¹ * y * gc ∈ T := (hBgc y).mp hy
    have hy'T : gc⁻¹ * y' * gc ∈ T := (hBgc y').mp hy'
    have hcommT : (gc⁻¹ * y * gc) * (gc⁻¹ * y' * gc) =
        (gc⁻¹ * y' * gc) * (gc⁻¹ * y * gc) := hab _ hyT _ hy'T
    have h1 : gc * ((gc⁻¹ * y * gc) * (gc⁻¹ * y' * gc)) * gc⁻¹ = y * y' := by group
    have h2 : gc * ((gc⁻¹ * y' * gc) * (gc⁻¹ * y * gc)) * gc⁻¹ = y' * y := by group
    rw [← h1, hcommT, h2]
  have hcA : (x * a * x⁻¹) ∈ centralizer ({a} : Set E) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have haB : a ∈ centralizer ({x * a * x⁻¹} : Set E) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  have hAB : centralizer ({a} : Set E) = centralizer ({x * a * x⁻¹} : Set E) := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hAcomm y hy (x * a * x⁻¹) hcA
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hBcomm y hy a haB
  have hconjiff : ∀ y, y * (x * a * x⁻¹) = (x * a * x⁻¹) * y ↔
      (x⁻¹ * y * x) * a = a * (x⁻¹ * y * x) := by
    intro y
    constructor
    · intro h
      have h1 : x⁻¹ * (y * (x * a * x⁻¹)) * x = (x⁻¹ * y * x) * a := by group
      have h2 : x⁻¹ * ((x * a * x⁻¹) * y) * x = a * (x⁻¹ * y * x) := by group
      rw [h] at h1
      rw [← h1, h2]
    · intro h
      have h1 : x * ((x⁻¹ * y * x) * a) * x⁻¹ = y * (x * a * x⁻¹) := by group
      have h2 : x * (a * (x⁻¹ * y * x)) * x⁻¹ = (x * a * x⁻¹) * y := by group
      rw [h] at h1
      rw [← h1, h2]
  have hBinv : ∀ y, y ∈ centralizer ({x * a * x⁻¹} : Set E) ↔
      x⁻¹ * y * x ∈ centralizer ({a} : Set E) := by
    intro y
    simp only [Subgroup.mem_centralizer_singleton_iff]
    exact hconjiff y
  have hmemAB : ∀ y, (y ∈ centralizer ({a} : Set E) ↔
      y ∈ centralizer ({x * a * x⁻¹} : Set E)) := by
    intro y; rw [hAB]
  have hAiff : ∀ y, y ∈ centralizer ({a} : Set E) ↔
      x⁻¹ * y * x ∈ centralizer ({a} : Set E) :=
    fun y => (hmemAB y).trans (hBinv y)
  have hAiff' : ∀ z, x * z * x⁻¹ ∈ centralizer ({a} : Set E) ↔
      z ∈ centralizer ({a} : Set E) := by
    intro z
    have h := hAiff (x * z * x⁻¹)
    have hz : x⁻¹ * (x * z * x⁻¹) * x = z := by group
    rwa [hz] at h
  have hstep1 : ∀ h, h ∈ T ↔ ga * h * ga⁻¹ ∈ centralizer ({a} : Set E) := by
    intro h
    have h1 := (hAga (ga * h * ga⁻¹)).symm
    have hgh : ga⁻¹ * (ga * h * ga⁻¹) * ga = h := by group
    rwa [hgh] at h1
  set w : E := ga⁻¹ * x * ga with hwdef
  have hwh : ∀ h, ga⁻¹ * (x * (ga * h * ga⁻¹) * x⁻¹) * ga = w * h * w⁻¹ := by
    intro h; rw [hwdef]; group
  have hwN : w ∈ normalizer (T : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    calc h ∈ T ↔ ga * h * ga⁻¹ ∈ centralizer ({a} : Set E) := hstep1 h
      _ ↔ x * (ga * h * ga⁻¹) * x⁻¹ ∈ centralizer ({a} : Set E) := (hAiff' _).symm
      _ ↔ ga⁻¹ * (x * (ga * h * ga⁻¹) * x⁻¹) * ga ∈ T := hAga _
      _ ↔ w * h * w⁻¹ ∈ T := by rw [hwh h]
  have hw3 : w ^ 3 = 1 := by
    have hp : w ^ 3 = ga⁻¹ * x ^ 3 * ga := by
      rw [hwdef]
      simpa using conj_pow (a := ga⁻¹) (b := x) (i := 3)
    rw [hp, hx]; group
  have hwT : w ∈ T := hN3 w hwN hw3
  have hw8 : w ^ 8 = 1 := by
    have h := pow_card_eq_one' (G := T) (x := ⟨w, hwT⟩)
    rw [hT] at h
    simpa using congrArg (fun z : T => (z : E)) h
  have hw9 : w ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hw3, one_pow]
  have hw_eq : w ^ 9 = w := by
    rw [show (9 : ℕ) = 8 + 1 by norm_num, pow_add, hw8, one_mul, pow_one]
  have hw1 : w = 1 := by rw [← hw_eq]; exact hw9
  have hx_eq : x = 1 := by
    have h := congrArg (fun z => ga * z * ga⁻¹) hw1
    rw [hwdef] at h
    have key : ga * (ga⁻¹ * x * ga) * ga⁻¹ = x := by group
    rw [key] at h
    simpa using h
  exact hx1 hx_eq

end CFSG.GroupTheory.SmallFixedTwoGroup
