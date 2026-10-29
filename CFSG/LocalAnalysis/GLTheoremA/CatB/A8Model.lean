module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09A8Core

public section

set_option maxHeartbeats 400000

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Equiv Equiv.Perm Subgroup

abbrev A8 : Type := ↥(alternatingGroup (Fin 8))

@[expose] def a8c : Perm (Fin 8) := swap 0 1 * swap 1 2
@[expose] def a8d : Perm (Fin 8) := swap 3 4 * swap 4 5
@[expose] def a8w1 : Perm (Fin 8) := swap 0 1 * swap 2 7
@[expose] def a8w2 : Perm (Fin 8) := swap 0 2 * swap 1 7
@[expose] def a8w3 : Perm (Fin 8) := swap 3 4 * swap 5 6
@[expose] def a8w4 : Perm (Fin 8) := swap 3 5 * swap 4 6

theorem sign_swap_mul_swap {a b c d : Fin 8} (h1 : a ≠ b) (h2 : c ≠ d) :
    Equiv.Perm.sign (swap a b * swap c d) = 1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h1, Equiv.Perm.sign_swap h2]
  rfl

theorem a8c_sign : Equiv.Perm.sign a8c = 1 :=
  sign_swap_mul_swap (a := 0) (b := 1) (c := 1) (d := 2) (by decide) (by decide)
theorem a8d_sign : Equiv.Perm.sign a8d = 1 :=
  sign_swap_mul_swap (a := 3) (b := 4) (c := 4) (d := 5) (by decide) (by decide)
theorem a8w1_sign : Equiv.Perm.sign a8w1 = 1 :=
  sign_swap_mul_swap (a := 0) (b := 1) (c := 2) (d := 7) (by decide) (by decide)
theorem a8w2_sign : Equiv.Perm.sign a8w2 = 1 :=
  sign_swap_mul_swap (a := 0) (b := 2) (c := 1) (d := 7) (by decide) (by decide)
theorem a8w3_sign : Equiv.Perm.sign a8w3 = 1 :=
  sign_swap_mul_swap (a := 3) (b := 4) (c := 5) (d := 6) (by decide) (by decide)
theorem a8w4_sign : Equiv.Perm.sign a8w4 = 1 :=
  sign_swap_mul_swap (a := 3) (b := 5) (c := 4) (d := 6) (by decide) (by decide)

@[expose] def toA8 (σ : Perm (Fin 8)) (h : Equiv.Perm.sign σ = 1) : A8 :=
  ⟨σ, Equiv.Perm.mem_alternatingGroup.2 h⟩

@[expose] def a8c8 : A8 := toA8 a8c a8c_sign
@[expose] def a8d8 : A8 := toA8 a8d a8d_sign
@[expose] def a8v1 : A8 := toA8 a8w1 a8w1_sign
@[expose] def a8v2 : A8 := toA8 a8w2 a8w2_sign
@[expose] def a8v3 : A8 := toA8 a8w3 a8w3_sign
@[expose] def a8v4 : A8 := toA8 a8w4 a8w4_sign

@[expose] def a8P0 : Subgroup A8 := closure {a8c8, a8d8}

@[expose] def a8V0 : Subgroup A8 := closure {a8v1, a8v2, a8v3, a8v4}

theorem a8c8_mem_P0 : a8c8 ∈ a8P0 := subset_closure (by simp [a8P0])
theorem a8d8_mem_P0 : a8d8 ∈ a8P0 := subset_closure (by simp [a8P0])
theorem a8v1_mem_V0 : a8v1 ∈ a8V0 := subset_closure (by simp [a8V0])
theorem a8v2_mem_V0 : a8v2 ∈ a8V0 := subset_closure (by simp [a8V0])
theorem a8v3_mem_V0 : a8v3 ∈ a8V0 := subset_closure (by simp [a8V0])
theorem a8v4_mem_V0 : a8v4 ∈ a8V0 := subset_closure (by simp [a8V0])

theorem a8c_apply0 : a8c 0 = 1 := by decide
theorem a8c_apply1 : a8c 1 = 2 := by decide
theorem a8c_apply2 : a8c 2 = 0 := by decide
theorem a8c_fix : ∀ y : Fin 8, 3 ≤ y.val → a8c y = y := by decide
theorem fin8_lt3 : ∀ w : Fin 8, w.val < 3 ↔ w = 0 ∨ w = 1 ∨ w = 2 := by decide

theorem a8c_cube : a8c ^ 3 = 1 := Equiv.ext (by decide)
theorem a8d_cube : a8d ^ 3 = 1 := Equiv.ext (by decide)

theorem a8c8_cube : a8c8 ^ 3 = 1 := Subtype.ext a8c_cube
theorem a8d8_cube : a8d8 ^ 3 = 1 := Subtype.ext a8d_cube

theorem a8c8_ne_one : a8c8 ≠ 1 := fun h =>
  absurd (congrArg (fun z : A8 => (z : Perm (Fin 8)) 0) h) (by decide)

theorem a8v1_ne_one : a8v1 ≠ 1 := fun h =>
  absurd (congrArg (fun z : A8 => (z : Perm (Fin 8)) 0) h) (by decide)

theorem a8c8_val : ((a8c8 : A8) : Perm (Fin 8)) = a8c := rfl

theorem a8c8_orderOf : orderOf a8c8 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime a8c8_cube a8c8_ne_one

theorem a8_nontriv : a8c8 * a8v1 * a8c8⁻¹ ≠ a8v1 := fun h =>
  absurd (congrArg (fun z : A8 => (z : Perm (Fin 8)) 0) h) (by decide)

theorem a8_card : Nat.card A8 = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem a8_center : Subgroup.center A8 = ⊥ :=
  alternatingGroup.center_eq_bot (by simp)

theorem a8_three_part_perm : ∀ n : ℕ, 3 ^ n ∣ 20160 → n ≤ 2 := by
  intro n hn
  by_contra h
  have : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
  have := this.trans hn
  norm_num at this

theorem a8c8_conj_v1 : a8c8 * a8v1 * a8c8⁻¹ = a8v1 * a8v2 := Subtype.ext (Equiv.ext (by decide))
theorem a8c8_conj_v2 : a8c8 * a8v2 * a8c8⁻¹ = a8v1 := Subtype.ext (Equiv.ext (by decide))
theorem a8c8_conj_v3 : a8c8 * a8v3 * a8c8⁻¹ = a8v3 := Subtype.ext (Equiv.ext (by decide))
theorem a8c8_conj_v4 : a8c8 * a8v4 * a8c8⁻¹ = a8v4 := Subtype.ext (Equiv.ext (by decide))
theorem a8c8_inv_v1 : a8c8⁻¹ * a8v1 * a8c8⁻¹⁻¹ = a8v2 := Subtype.ext (Equiv.ext (by decide))
theorem a8c8_inv_v2 : a8c8⁻¹ * a8v2 * a8c8⁻¹⁻¹ = a8v1 * a8v2 :=
  Subtype.ext (Equiv.ext (by decide))
theorem a8c8_inv_v3 : a8c8⁻¹ * a8v3 * a8c8⁻¹⁻¹ = a8v3 := Subtype.ext (Equiv.ext (by decide))
theorem a8c8_inv_v4 : a8c8⁻¹ * a8v4 * a8c8⁻¹⁻¹ = a8v4 := Subtype.ext (Equiv.ext (by decide))
theorem a8d8_conj_v3 : a8d8 * a8v3 * a8d8⁻¹ = a8v3 * a8v4 := Subtype.ext (Equiv.ext (by decide))
theorem a8d8_conj_v4 : a8d8 * a8v4 * a8d8⁻¹ = a8v3 := Subtype.ext (Equiv.ext (by decide))
theorem a8d8_conj_v1 : a8d8 * a8v1 * a8d8⁻¹ = a8v1 := Subtype.ext (Equiv.ext (by decide))
theorem a8d8_conj_v2 : a8d8 * a8v2 * a8d8⁻¹ = a8v2 := Subtype.ext (Equiv.ext (by decide))
theorem a8d8_inv_v3 : a8d8⁻¹ * a8v3 * a8d8⁻¹⁻¹ = a8v4 := Subtype.ext (Equiv.ext (by decide))
theorem a8d8_inv_v4 : a8d8⁻¹ * a8v4 * a8d8⁻¹⁻¹ = a8v3 * a8v4 :=
  Subtype.ext (Equiv.ext (by decide))
theorem a8d8_inv_v1 : a8d8⁻¹ * a8v1 * a8d8⁻¹⁻¹ = a8v1 := Subtype.ext (Equiv.ext (by decide))
theorem a8d8_inv_v2 : a8d8⁻¹ * a8v2 * a8d8⁻¹⁻¹ = a8v2 := Subtype.ext (Equiv.ext (by decide))

theorem conj_mem_closure {S : Set A8} (g : A8) (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ closure S) :
    ∀ v ∈ closure S, g * v * g⁻¹ ∈ closure S := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem c_fwd : ∀ s ∈ ({a8v1, a8v2, a8v3, a8v4} : Set A8), a8c8 * s * a8c8⁻¹ ∈ a8V0 := by
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [a8c8_conj_v1]; exact mul_mem a8v1_mem_V0 a8v2_mem_V0
  · rw [a8c8_conj_v2]; exact a8v1_mem_V0
  · rw [a8c8_conj_v3]; exact a8v3_mem_V0
  · rw [a8c8_conj_v4]; exact a8v4_mem_V0

theorem c_bwd : ∀ s ∈ ({a8v1, a8v2, a8v3, a8v4} : Set A8), a8c8⁻¹ * s * a8c8⁻¹⁻¹ ∈ a8V0 := by
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [a8c8_inv_v1]; exact a8v2_mem_V0
  · rw [a8c8_inv_v2]; exact mul_mem a8v1_mem_V0 a8v2_mem_V0
  · rw [a8c8_inv_v3]; exact a8v3_mem_V0
  · rw [a8c8_inv_v4]; exact a8v4_mem_V0

theorem d_fwd : ∀ s ∈ ({a8v1, a8v2, a8v3, a8v4} : Set A8), a8d8 * s * a8d8⁻¹ ∈ a8V0 := by
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [a8d8_conj_v1]; exact a8v1_mem_V0
  · rw [a8d8_conj_v2]; exact a8v2_mem_V0
  · rw [a8d8_conj_v3]; exact mul_mem a8v3_mem_V0 a8v4_mem_V0
  · rw [a8d8_conj_v4]; exact a8v3_mem_V0

theorem d_bwd : ∀ s ∈ ({a8v1, a8v2, a8v3, a8v4} : Set A8), a8d8⁻¹ * s * a8d8⁻¹⁻¹ ∈ a8V0 := by
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [a8d8_inv_v1]; exact a8v1_mem_V0
  · rw [a8d8_inv_v2]; exact a8v2_mem_V0
  · rw [a8d8_inv_v3]; exact a8v4_mem_V0
  · rw [a8d8_inv_v4]; exact mul_mem a8v3_mem_V0 a8v4_mem_V0

theorem a8c8_mem_normalizer : a8c8 ∈ Subgroup.normalizer (a8V0 : Set A8) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_closure _ c_fwd h hh, fun hh => ?_⟩
  have e : a8c8⁻¹ * (a8c8 * h * a8c8⁻¹) * a8c8⁻¹⁻¹ = h := by group
  have := conj_mem_closure _ c_bwd _ hh
  rwa [e] at this

theorem a8d8_mem_normalizer : a8d8 ∈ Subgroup.normalizer (a8V0 : Set A8) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_closure _ d_fwd h hh, fun hh => ?_⟩
  have e : a8d8⁻¹ * (a8d8 * h * a8d8⁻¹) * a8d8⁻¹⁻¹ = h := by group
  have := conj_mem_closure _ d_bwd _ hh
  rwa [e] at this

theorem a8P0_le_normalizer : a8P0 ≤ Subgroup.normalizer (a8V0 : Set A8) := by
  unfold a8P0
  rw [Subgroup.closure_le]
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · exact a8c8_mem_normalizer
  · exact a8d8_mem_normalizer

theorem a8_normalizes {p v : A8} (hp : p ∈ a8P0) (hv : v ∈ a8V0) : p * v * p⁻¹ ∈ a8V0 :=
  (Subgroup.mem_normalizer_iff.1 (a8P0_le_normalizer hp) v).1 hv

theorem isPGroup_three_of_pow {H : Type*} [Group H] (h : ∀ x : H, x ^ 3 = 1) : IsPGroup 3 H :=
  fun g => ⟨1, by simpa using h g⟩

theorem isPGroup_closure_three {H : Type*} [Group H] (S : Set H) (hpow : ∀ s ∈ S, s ^ 3 = 1)
    (hc : ∀ s ∈ S, ∀ u ∈ S, s * u = u * s) : IsPGroup 3 (closure S) := by
  have h1 : ∀ x ∈ closure S, ∀ s ∈ S, x * s = s * x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact fun s hs => hc x hx s hs
    | one => exact fun s _ => by simp
    | mul x y _ _ hx hy =>
      exact fun s hs => by rw [mul_assoc, hy s hs, ← mul_assoc, hx s hs, mul_assoc]
    | inv x _ hx => exact fun s hs => (Commute.inv_left (hx s hs : Commute x s))
  have h2 : ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h1 x hx y hy
    | one => simp
    | mul y z _ _ hy hz => rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]
    | inv y _ hy => exact (Commute.inv_right (hy : Commute x y))
  have h3 : ∀ x ∈ closure S, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hpow x hx
    | one => simp
    | mul x y hx' hy hx hy' =>
      rw [(show Commute x y from h2 x hx' y hy).mul_pow 3, hx, hy', one_mul]
    | inv x hx' hx => rw [inv_pow, hx, inv_one]
  exact isPGroup_three_of_pow fun x : closure S => Subtype.ext (h3 x.1 x.2)

theorem a8P0_three : IsPGroup 3 a8P0 := by
  unfold a8P0
  refine isPGroup_closure_three _ (fun s hs => ?_) (fun s hs u hu => ?_)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact a8c8_cube
    · exact a8d8_cube
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hu
    rcases hs with rfl | rfl <;> rcases hu with rfl | rfl <;>
      exact Subtype.ext (Equiv.ext (by decide))

theorem a8P0_le9 : Nat.card a8P0 ≤ 9 := by
  obtain ⟨n, hn⟩ := a8P0_three.exists_card_eq
  have hd : 3 ^ n ∣ 20160 := by
    rw [← a8_card, ← hn]; exact Subgroup.card_subgroup_dvd_card _
  rw [hn]
  exact le_trans (Nat.pow_le_pow_right (by norm_num) (a8_three_part_perm n hd)) (by norm_num)

theorem nine_le_P0 : 9 ≤ Nat.card a8P0 := by
  let g : Fin 3 × Fin 3 → A8 := fun a => a8c8 ^ (a.1 : ℕ) * a8d8 ^ (a.2 : ℕ)
  have hg : ∀ a, g a ∈ a8P0 := fun a =>
    mul_mem (pow_mem a8c8_mem_P0 _) (pow_mem a8d8_mem_P0 _)
  have hev : Function.Injective
      (fun a : Fin 3 × Fin 3 => (((a8c ^ (a.1 : ℕ) * a8d ^ (a.2 : ℕ)) 0,
        (a8c ^ (a.1 : ℕ) * a8d ^ (a.2 : ℕ)) 3) : Fin 8 × Fin 8)) := by decide
  have hinj : Function.Injective (fun a => (⟨g a, hg a⟩ : a8P0)) := by
    intro a b hab
    have h1 : g a = g b := congrArg Subtype.val hab
    apply hev
    exact congrArg (fun x : A8 => ((x : Perm (Fin 8)) 0, (x : Perm (Fin 8)) 3)) h1
  calc 9 = Nat.card (Fin 3 × Fin 3) := by simp
    _ ≤ Nat.card a8P0 := Nat.card_le_card_of_injective _ hinj

theorem a8P0_card : Nat.card a8P0 = 9 := le_antisymm a8P0_le9 nine_le_P0

@[expose] def a8X : Fin 3 → A8 := ![1, a8v1, a8v2]
@[expose] def a8Y : Fin 3 → A8 := ![1, a8v3, a8v4]

theorem a8X_mem (i : Fin 3) : a8X i ∈ a8V0 := by
  fin_cases i <;> simp [a8X, a8v1_mem_V0, a8v2_mem_V0]

theorem a8Y_mem (i : Fin 3) : a8Y i ∈ a8V0 := by
  fin_cases i <;> simp [a8Y, a8v3_mem_V0, a8v4_mem_V0]

theorem nine_le_V0 : 9 ≤ Nat.card a8V0 := by
  have hmem : ∀ a : Fin 3 × Fin 3, a8X a.1 * a8Y a.2 ∈ a8V0 := fun a =>
    mul_mem (a8X_mem a.1) (a8Y_mem a.2)
  have hev : Function.Injective
      (fun a : Fin 3 × Fin 3 => ((((a8X a.1 * a8Y a.2 : A8)) : Perm (Fin 8)) 0,
        ((a8X a.1 * a8Y a.2 : A8) : Perm (Fin 8)) 3)) := by decide
  have hinj : Function.Injective (fun a : Fin 3 × Fin 3 => (⟨a8X a.1 * a8Y a.2, hmem a⟩ : a8V0)) := by
    intro a b hab
    have h1 : a8X a.1 * a8Y a.2 = a8X b.1 * a8Y b.2 := congrArg Subtype.val hab
    apply hev
    exact congrArg (fun z : A8 => ((z : Perm (Fin 8)) 0, (z : Perm (Fin 8)) 3)) h1
  calc 9 = Nat.card (Fin 3 × Fin 3) := by simp
    _ ≤ Nat.card a8V0 := Nat.card_le_card_of_injective _ hinj

theorem a8V0_two : IsPGroup 2 a8V0 := by
  refine a8_pair2 _ (fun s hs => ?_) (fun s hs u hu => ?_)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> exact Subtype.ext (Equiv.ext (by decide))
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hu
    rcases hs with rfl | rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl | rfl <;>
      exact Subtype.ext (Equiv.ext (by decide))

theorem a8V0_big : 9 ≤ Nat.card a8V0 := nine_le_V0

@[expose] def fin5e : Fin 5 ≃ {x : Fin 8 // 3 ≤ x.val} where
  toFun i := ⟨⟨i.val + 3, by have := i.isLt; omega⟩, by simp⟩
  invFun x := ⟨x.1.val - 3, by have := x.1.isLt; have := x.2; omega⟩
  left_inv i := Fin.ext (by simp)
  right_inv x := Subtype.ext (Fin.ext (by have := x.2; show x.1.val - 3 + 3 = x.1.val; omega))

@[expose] def a8ι : alternatingGroup (Fin 5) →* A8 :=
  ((Equiv.Perm.extendDomainHom fin5e).comp (alternatingGroup (Fin 5)).subtype).codRestrict
    (alternatingGroup (Fin 8)) fun σ =>
      Equiv.Perm.mem_alternatingGroup.2
        ((Equiv.Perm.sign_extendDomain σ.1 fin5e).trans (Equiv.Perm.mem_alternatingGroup.1 σ.2))

@[expose] def a8Kb : Subgroup A8 := a8ι.range

theorem a8ι_injective : Function.Injective a8ι := by
  intro x y h
  apply Subtype.ext
  exact Equiv.Perm.extendDomainHom_injective fin5e
    (congrArg (fun z : A8 => (z : Perm (Fin 8))) h)

@[expose] noncomputable def a8KbEquiv : alternatingGroup (Fin 5) ≃* a8Kb :=
  MonoidHom.ofInjective a8ι_injective

theorem a8Kb_simple : IsSimpleGroup a8Kb := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance
  exact MulEquiv.isSimpleGroup a8KbEquiv.symm

theorem a8Kb_card : Nat.card a8Kb = 60 := by
  rw [← Nat.card_congr a8KbEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem a8Kb_nonabelian : ¬ IsMulCommutative a8Kb := by
  intro h
  let x : alternatingGroup (Fin 5) :=
    ⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩
  let y : alternatingGroup (Fin 5) :=
    ⟨swap 0 1 * swap 2 3, Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩
  have hxy : x * y ≠ y * x := by
    intro h'
    have h'' : swap (0 : Fin 5) 1 * swap (1 : Fin 5) 2 * (swap (0 : Fin 5) 1 * swap (2 : Fin 5) 3) =
        swap (0 : Fin 5) 1 * swap (2 : Fin 5) 3 * (swap (0 : Fin 5) 1 * swap (1 : Fin 5) 2) :=
      congrArg Subtype.val h'
    exact absurd h'' (by decide +kernel)
  apply hxy
  apply a8KbEquiv.injective
  rw [map_mul, map_mul]
  exact h.is_comm.comm _ _

theorem mem_a8Kb_iff (x : A8) :
    x ∈ a8Kb ↔ (x : Perm (Fin 8)) 0 = 0 ∧ (x : Perm (Fin 8)) 1 = 1 ∧ (x : Perm (Fin 8)) 2 = 2 := by
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      exact Equiv.Perm.extendDomain_apply_not_subtype _ _ (p := fun z : Fin 8 => 3 ≤ z.val)
        (by decide)
  · rintro ⟨h0, h1, h2⟩
    have hfix : ∀ w : Fin 8, w.val < 3 → (x : Perm (Fin 8)) w = w := by
      intro w hw
      rcases (fin8_lt3 w).1 hw with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
    have hp : ∀ z : Fin 8, 3 ≤ z.val ↔ 3 ≤ ((x : Perm (Fin 8)) z).val := by
      intro z
      constructor
      · intro hz
        by_contra hlt
        push Not at hlt
        have h1' := (x : Perm (Fin 8)).injective (hfix _ hlt)
        rw [h1'] at hlt
        omega
      · intro hz
        by_contra hlt
        push Not at hlt
        rw [hfix z hlt] at hz
        omega
    let sub := (x : Perm (Fin 8)).subtypePerm (p := fun z : Fin 8 => 3 ≤ z.val) (fun z => (hp z).symm)
    let σ : Perm (Fin 5) := fin5e.symm.permCongr sub
    have hσ : ∀ i, (σ i : Fin 5) = fin5e.symm (sub (fin5e i)) := fun i => rfl
    have hext : Equiv.Perm.extendDomain σ fin5e = (x : Perm (Fin 8)) := by
      ext z
      by_cases hz : 3 ≤ z.val
      · obtain ⟨i, hi⟩ : ∃ i, fin5e i = ⟨z, hz⟩ := ⟨fin5e.symm ⟨z, hz⟩, by simp⟩
        have hz8 : ((fin5e i : {x : Fin 8 // 3 ≤ x.val}) : Fin 8) = z := congrArg Subtype.val hi
        have key := Equiv.Perm.extendDomain_apply_image σ fin5e i
        rw [hz8] at key
        rw [key, hσ]
        simp [sub, Equiv.Perm.subtypePerm_apply, hz8]
      · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ (p := fun z : Fin 8 => 3 ≤ z.val) hz]
        exact congrArg Fin.val (hfix z (by omega)).symm
    have hsign : Equiv.Perm.sign σ = 1 := by
      rw [← Equiv.Perm.sign_extendDomain σ fin5e, hext]
      exact Equiv.Perm.mem_alternatingGroup.1 x.2
    exact MonoidHom.mem_range.2 ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.2 hsign⟩,
      Subtype.ext hext⟩

theorem perm_comm_of_fix (k : Perm (Fin 8)) (h0 : k 0 = 0) (h1 : k 1 = 1) (h2 : k 2 = 2) :
    a8c * k = k * a8c := by
  have hfix : ∀ w : Fin 8, w.val < 3 → k w = w := by
    intro w hw
    rcases (fin8_lt3 w).1 hw with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  have hge : ∀ y : Fin 8, 3 ≤ y.val → 3 ≤ (k y).val := by
    intro y hy
    by_contra hlt
    push Not at hlt
    have hk : k (k y) = k y := hfix _ hlt
    have hyk : y = k y := k.injective hk.symm
    rw [← hyk] at hlt
    omega
  ext y
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hy : 3 ≤ y.val
  · rw [a8c_fix y hy, a8c_fix (k y) (hge y hy)]
  · rcases (by omega : y.val = 0 ∨ y.val = 1 ∨ y.val = 2) with e | e | e
    · obtain rfl : y = 0 := Fin.ext e
      rw [h0, a8c_apply0, h1]
    · obtain rfl : y = 1 := Fin.ext e
      rw [h1, a8c_apply1, h2]
    · obtain rfl : y = 2 := Fin.ext e
      rw [h2, a8c_apply2, h0]

theorem a8Kb_le_centralizer : a8Kb ≤ Subgroup.centralizer ({a8c8} : Set A8) := by
  intro k hk
  obtain ⟨h0, h1, h2⟩ := (mem_a8Kb_iff k).1 hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  exact (perm_comm_of_fix _ h0 h1 h2).symm

theorem a8_centralizer : Subgroup.centralizer ({a8c8} : Set A8) = a8Kb ⊔ Subgroup.zpowers a8c8 := by
  refine le_antisymm ?_ (sup_le a8Kb_le_centralizer
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)))
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hxc : (x : Perm (Fin 8)) * a8c = a8c * (x : Perm (Fin 8)) := congrArg Subtype.val hx
  have hcomm0 : a8c ((x : Perm (Fin 8)) 0) = (x : Perm (Fin 8)) 1 := by
    have := congrArg (fun f : Perm (Fin 8) => f 0) hxc
    simp only [Perm.mul_apply, a8c_apply0] at this
    exact this.symm
  have hx0 : (x : Perm (Fin 8)) 0 = 0 ∨ (x : Perm (Fin 8)) 0 = 1 ∨ (x : Perm (Fin 8)) 0 = 2 := by
    by_contra hne
    push Not at hne
    have h3 : 3 ≤ ((x : Perm (Fin 8)) 0).val := by
      by_contra hlt
      push Not at hlt
      rcases (fin8_lt3 _).1 hlt with e | e | e
      · exact hne.1 e
      · exact hne.2.1 e
      · exact hne.2.2 e
    have h1' : (x : Perm (Fin 8)) 1 = (x : Perm (Fin 8)) 0 := by
      rw [← hcomm0, a8c_fix _ h3]
    exact absurd ((x : Perm (Fin 8)).injective h1') (by decide)
  obtain ⟨j, hj3, hj⟩ : ∃ j : ℕ, j < 3 ∧ (a8c ^ j) 0 = (x : Perm (Fin 8)) 0 := by
    rcases hx0 with e | e | e
    · exact ⟨0, by norm_num, by simp [e]⟩
    · exact ⟨1, by norm_num, by simp [e, a8c_apply0]⟩
    · exact ⟨2, by norm_num, by simp [e, pow_two, Perm.mul_apply, a8c_apply0, a8c_apply1]⟩
  have hcp : a8c * (a8c ^ j)⁻¹ = (a8c ^ j)⁻¹ * a8c :=
    ((Commute.refl a8c).pow_right j).inv_right.eq
  obtain ⟨k, hkdef⟩ : ∃ k : Perm (Fin 8), k = (a8c ^ j)⁻¹ * (x : Perm (Fin 8)) := ⟨_, rfl⟩
  have hk_comm : a8c * k = k * a8c := by
    rw [hkdef, ← mul_assoc, hcp, mul_assoc, ← hxc, mul_assoc]
  have hk0 : k 0 = 0 := by
    rw [hkdef, Perm.mul_apply, ← hj]; simp
  have e0 := congrArg (fun f : Perm (Fin 8) => f 0) hk_comm
  simp only [Perm.mul_apply] at e0
  rw [hk0, a8c_apply0] at e0
  have hk1 : k 1 = 1 := e0.symm
  have e1 := congrArg (fun f : Perm (Fin 8) => f 1) hk_comm
  simp only [Perm.mul_apply] at e1
  rw [hk1, a8c_apply1] at e1
  have hk2 : k 2 = 2 := e1.symm
  have hkA : (((a8c8 ^ j)⁻¹ * x : A8) : Perm (Fin 8)) = k := by
    rw [hkdef]; rfl
  have hkK : (a8c8 ^ j)⁻¹ * x ∈ a8Kb :=
    (mem_a8Kb_iff _).2 ⟨by rw [hkA]; exact hk0, by rw [hkA]; exact hk1, by rw [hkA]; exact hk2⟩
  have key : a8c8 ^ j * ((a8c8 ^ j)⁻¹ * x) ∈ Subgroup.zpowers a8c8 ⊔ a8Kb :=
    Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers a8c8) j) hkK
  rwa [mul_inv_cancel_left, sup_comm] at key

theorem a8Kb_inf_zpowers : a8Kb ⊓ Subgroup.zpowers a8c8 = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxZ⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxZ
  have hn : a8c8 ^ (n % 3) = a8c8 ^ n := by
    have h := zpow_mod_orderOf a8c8 n
    rw [a8c8_orderOf] at h
    exact_mod_cast h
  have hm0 : 0 ≤ n % 3 := Int.emod_nonneg _ (by norm_num)
  have hm3 : n % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  rw [← hn] at hxK ⊢
  rw [Subgroup.mem_bot]
  generalize n % 3 = m at hm0 hm3 hxK ⊢
  interval_cases m
  · simp
  · exfalso
    have h0 := ((mem_a8Kb_iff _).1 hxK).1
    simp [a8c8_val, a8c_apply0] at h0
  · exfalso
    have h0 := ((mem_a8Kb_iff _).1 hxK).1
    simp [a8c8_val, pow_two, Perm.mul_apply, a8c_apply0, a8c_apply1] at h0

end CFSG.LocalAnalysis.GLTheoremA.CatB
