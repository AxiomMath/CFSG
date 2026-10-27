module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.N1Core

open Subgroup

theorem conj_injective {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  refine (injective_iff_map_eq_one _).2 fun a ha => ?_
  have hmem : a ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (MulAut.conj a) g = g := by rw [ha]; rfl
    rw [MulAut.conj_apply] at h1
    calc g * a = (a * g * a⁻¹) * a := by rw [h1]
      _ = a * g := by group
  rw [hZ] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem inner_of_odd_order {K : Type*} [Group K] (hZ : Subgroup.center K = ⊥) [Finite K]
    (hcard : Nat.card (MulAut K) = 2 * Nat.card K) {b : MulAut K} (hb : Odd (orderOf b)) :
    ∃ y : K, b = MulAut.conj y := by
  have hinj := conj_injective hZ
  let I : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range
  have hIcard : Nat.card ↥I = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hindex : I.index = 2 := by
    have h1 := Subgroup.card_mul_index I
    rw [hIcard, hcard] at h1
    have hpos : 0 < Nat.card K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))
  have hnorm : I.Normal := Subgroup.normal_of_index_eq_two hindex
  have hsq : b ^ 2 ∈ I := by
    have := Subgroup.pow_index_mem I b
    rwa [hindex] at this
  obtain ⟨k, hk⟩ := hb
  have hbk : b ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one b
  have hbe : b = (b ^ 2) ^ (k + 1) := by
    calc b = b ^ (2 * k + 1) * b := by rw [hbk, one_mul]
      _ = (b ^ 2) ^ (k + 1) := by rw [← pow_succ, ← pow_mul]; ring_nf
  have hbI : b ∈ I := by
    rw [hbe]
    exact pow_mem hsq (k + 1)
  obtain ⟨y, hy⟩ := hbI
  exact ⟨y, hy.symm⟩

theorem n1_core {Y : Type*} [Group Y] {p : ℕ} [Fact p.Prime] {b : MulAut Y}
    (hb : orderOf b = p) {R₀ : Subgroup Y}
    (hpg : IsPGroup p ↥(closure {c : MulAut Y | ∃ r ∈ R₀,
      c = MulAut.conj r * b * (MulAut.conj r)⁻¹})) {y : Y} (hy : b = MulAut.conj y)
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) :
    y ≠ 1 ∧ y ^ p = 1 ∧ ∃ X : Subgroup Y, IsPGroup p ↥X ∧ y ∈ X ∧ R₀ ≤ normalizer (X : Set Y) := by
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [hy, map_one, orderOf_one] at hb
    exact (Fact.out : p.Prime).one_lt.ne hb
  have hyp : y ^ p = 1 := by
    apply hinj
    rw [map_pow, ← hy, ← hb, pow_orderOf_eq_one, map_one]
  refine ⟨hy1, hyp, ?_⟩
  obtain ⟨S, hS⟩ : ∃ S : Set Y, S = {x | ∃ r ∈ R₀, x = r * y * r⁻¹} := ⟨_, rfl⟩
  have hSmem : ∀ x, x ∈ S ↔ ∃ r ∈ R₀, x = r * y * r⁻¹ := fun x => by rw [hS]; rfl
  have hmap : (closure S).map (MulAut.conj : Y →* MulAut Y) =
      closure {c : MulAut Y | ∃ r ∈ R₀, c = MulAut.conj r * b * (MulAut.conj r)⁻¹} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨r, hr, rfl⟩ := (hSmem x).1 hx
      exact ⟨r, hr, by rw [hy, map_mul, map_mul, map_inv]⟩
    · rintro ⟨r, hr, rfl⟩
      refine ⟨r * y * r⁻¹, (hSmem _).2 ⟨r, hr, rfl⟩, ?_⟩
      rw [hy, map_mul, map_mul, map_inv]
  have hXp : IsPGroup p ↥(closure S) := by
    have h1 : IsPGroup p ↥((closure S).map (MulAut.conj : Y →* MulAut Y)) := by
      rw [hmap]
      exact hpg
    exact h1.of_equiv ((closure S).equivMapOfInjective _ hinj).symm
  have hyX : y ∈ closure S := subset_closure ((hSmem y).2 ⟨1, R₀.one_mem, by simp⟩)
  have hconj : ∀ r ∈ R₀, ∀ x ∈ closure S, r * x * r⁻¹ ∈ closure S := by
    intro r hr x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨r', hr', rfl⟩ := (hSmem x).1 hx
      refine subset_closure ((hSmem _).2 ⟨r * r', R₀.mul_mem hr hr', ?_⟩)
      group
    | one => simp
    | mul x z _ _ hx hz =>
      have : r * (x * z) * r⁻¹ = (r * x * r⁻¹) * (r * z * r⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hz
    | inv x _ hx =>
      have : r * x⁻¹ * r⁻¹ = (r * x * r⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  have hN : R₀ ≤ normalizer ((closure S : Subgroup Y) : Set Y) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj r hr h, fun hh => ?_⟩
    have h1 := hconj r⁻¹ (R₀.inv_mem hr) _ hh
    have h2 : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ = h := by group
    rwa [h2] at h1
  exact ⟨closure S, hXp, hyX, hN⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.N1Core
