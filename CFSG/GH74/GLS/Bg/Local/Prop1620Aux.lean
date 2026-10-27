module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.Bg.Glauberman

open Subgroup

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {A : Subgroup G} {g : G}
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  have hinj : Function.Injective (fun a : A => (⟨g * a * g⁻¹, h a a.2⟩ : A)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  obtain ⟨⟨y, hy⟩, hyx⟩ := hsurj ⟨g * x * g⁻¹, hx⟩
  have := congrArg Subtype.val hyx
  simp only [mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact hy

theorem exists_pow_two_pow_eq_one {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

@[expose] def stabSub (D B : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ normalizer (D : Set G) ∧ (∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ B) ∧
    ∀ b ∈ B, x * b = b * x}
  one_mem' := ⟨one_mem _, fun d _ => by simp, fun b _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxN, hxc, hxb⟩ ⟨hyN, hyc, hyb⟩
    refine ⟨mul_mem hxN hyN, fun d hd => ?_, fun b hb => ?_⟩
    · have h1 : x * (y * d * y⁻¹ * d⁻¹) * x⁻¹ = y * d * y⁻¹ * d⁻¹ := by
        have := hxb _ (hyc d hd)
        calc x * (y * d * y⁻¹ * d⁻¹) * x⁻¹ = (x * (y * d * y⁻¹ * d⁻¹)) * x⁻¹ := rfl
          _ = ((y * d * y⁻¹ * d⁻¹) * x) * x⁻¹ := by rw [this]
          _ = y * d * y⁻¹ * d⁻¹ := by group
      have h2 : x * y * d * (x * y)⁻¹ * d⁻¹ =
          (y * d * y⁻¹ * d⁻¹) * (x * d * x⁻¹ * d⁻¹) := by
        rw [← h1]; group
      rw [h2]
      exact mul_mem (hyc d hd) (hxc d hd)
    · rw [mul_assoc, hyb b hb, ← mul_assoc, hxb b hb, mul_assoc]
  inv_mem' := by
    rintro x ⟨hxN, hxc, hxb⟩
    refine ⟨inv_mem hxN, fun d hd => ?_, fun b hb => ?_⟩
    · have hd' : x⁻¹ * d * x ∈ D := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) d).mp hd
        simpa using this
      have h := hxc _ hd'
      have : x⁻¹ * d * x⁻¹⁻¹ * d⁻¹ = (x * (x⁻¹ * d * x) * x⁻¹ * (x⁻¹ * d * x)⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem h
    · have := hxb b hb
      calc x⁻¹ * b = x⁻¹ * (b * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * b) * x⁻¹ := by rw [this]
        _ = b * x⁻¹ := by group

theorem conj_mem_stabSub {D B : Subgroup G}
    (hB : ∀ y ∈ normalizer (D : Set G), ∀ b ∈ B, y * b * y⁻¹ ∈ B) {y t : G}
    (hy : y ∈ normalizer (D : Set G)) (ht : t ∈ stabSub D B) : y * t * y⁻¹ ∈ stabSub D B := by
  obtain ⟨htN, htc, htb⟩ := ht
  refine ⟨mul_mem (mul_mem hy htN) (inv_mem hy), fun d hd => ?_, fun b hb => ?_⟩
  · have hd' : y⁻¹ * d * y ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hy) d).mp hd
      simpa using this
    have h := hB y hy _ (htc _ hd')
    have : y * t * y⁻¹ * d * (y * t * y⁻¹)⁻¹ * d⁻¹ =
        y * (t * (y⁻¹ * d * y) * t⁻¹ * (y⁻¹ * d * y)⁻¹) * y⁻¹ := by group
    rw [this]
    exact h
  · have hb' : y⁻¹ * b * y ∈ B := by
      have := hB y⁻¹ (inv_mem hy) b hb
      simpa using this
    have h := htb _ hb'
    calc y * t * y⁻¹ * b = y * (t * (y⁻¹ * b * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * b * y) * t) * y⁻¹ := by rw [h]
      _ = b * (y * t * y⁻¹) := by group

theorem comm_of_odd_pow_eq_one {D B : Subgroup G} (hBD : B ≤ D)
    (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k = 1) {t : G} (ht : t ∈ stabSub D B) {m : ℕ}
    (hm : Odd m) (htm : t ^ m = 1) : ∀ d ∈ D, t * d = d * t := by
  intro d hd
  obtain ⟨_, hc, hb⟩ := ht
  have hβB : t * d * t⁻¹ * d⁻¹ ∈ B := hc d hd
  generalize hβ : t * d * t⁻¹ * d⁻¹ = β at hβB
  have htd : t * d * t⁻¹ = β * d := by rw [← hβ]; group
  have key : ∀ j : ℕ, t ^ j * d * (t ^ j)⁻¹ = β ^ j * d := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : t * β ^ j = β ^ j * t := hb _ (B.pow_mem hβB j)
      calc t ^ (j + 1) * d * (t ^ (j + 1))⁻¹
          = t * (t ^ j * d * (t ^ j)⁻¹) * t⁻¹ := by group
        _ = t * (β ^ j * d) * t⁻¹ := by rw [ih]
        _ = (t * β ^ j) * d * t⁻¹ := by group
        _ = (β ^ j * t) * d * t⁻¹ := by rw [h1]
        _ = β ^ j * (t * d * t⁻¹) := by group
        _ = β ^ (j + 1) * d := by rw [htd]; group
  have h2 := key m
  rw [htm] at h2
  have hβm : β ^ m = 1 := by
    have : d = β ^ m * d := by simpa using h2
    exact (mul_eq_right.mp this.symm)
  obtain ⟨k, hk⟩ := hD β (hBD hβB)
  have hβ1 : β = 1 := by
    have h3 : orderOf β ∣ m := orderOf_dvd_of_pow_eq_one hβm
    have h4 : orderOf β ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h3 h4)
  rw [hβ1] at htd
  exact mul_inv_eq_iff_eq_mul.mp (by simpa using htd)

theorem exists_pow_two_pow_comm [Finite G] {D B : Subgroup G} (hBD : B ≤ D)
    (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k = 1) {t : G} (ht : t ∈ stabSub D B) :
    ∃ k : ℕ, ∀ d ∈ D, t ^ 2 ^ k * d = d * t ^ 2 ^ k := by
  have hn : orderOf t ≠ 0 := (orderOf_pos t).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  refine ⟨k, comm_of_odd_pow_eq_one hBD hD ((stabSub D B).pow_mem ht _) hm ?_⟩
  rw [← pow_mul, ← hkm]
  exact pow_orderOf_eq_one t

theorem exists_mul_pow_eq {R : Subgroup G} {t : G} (ht : t ∈ normalizer (R : Set G)) {r : G}
    (hr : r ∈ R) : ∀ n : ℕ, ∃ r' ∈ R, (t * r) ^ n = t ^ n * r' := by
  intro n
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨r', hr', h⟩ := ih
    have hc : t⁻¹ * r' * t ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem ht) r').mp hr'
      simpa using this
    refine ⟨(t⁻¹ * r' * t) * r, mul_mem hc hr, ?_⟩
    calc (t * r) ^ (n + 1) = (t * r) ^ n * (t * r) := pow_succ _ _
      _ = t ^ n * r' * (t * r) := by rw [h]
      _ = t ^ (n + 1) * ((t⁻¹ * r' * t) * r) := by group

open scoped Pointwise in
theorem mem_sup_iff_mul {T R : Subgroup G} (hTR : T ≤ normalizer (R : Set G)) {x : G}
    (hx : x ∈ T ⊔ R) : ∃ t ∈ T, ∃ r ∈ R, x = t * r := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right T R hTR
  have hx' : x ∈ ((T : Set G) * (R : Set G)) := by rw [← h]; exact hx
  obtain ⟨t, ht, r, hr, rfl⟩ := hx'
  exact ⟨t, ht, r, hr, rfl⟩

end CFSG.GH74.GLS.Bg.Glauberman
