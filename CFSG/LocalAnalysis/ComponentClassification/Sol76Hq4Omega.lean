module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Cyc

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open Subgroup

theorem exists_two_mul_add {c : ℕ} (x : ZMod c) :
    ∃ (y : ZMod c) (i : Fin 2), x = 2 * y + (i : ℕ) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  have hk := Int.emod_add_mul_ediv k 2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · refine ⟨((k / 2 : ℤ) : ZMod c), 0, ?_⟩
    rw [h, zero_add] at hk
    conv_lhs => rw [← hk]
    simp only [Fin.val_zero, Nat.cast_zero, add_zero]
    push_cast
    ring
  · refine ⟨((k / 2 : ℤ) : ZMod c), 1, ?_⟩
    rw [h] at hk
    conv_lhs => rw [← hk]
    simp only [Fin.val_one, Nat.cast_one]
    push_cast
    ring

theorem exists_sq_mul {c : ℕ} (m : Multiplicative (ZMod c)) :
    ∃ (w : Multiplicative (ZMod c)) (i : Fin 2), m = w ^ 2 * Multiplicative.ofAdd 1 ^ (i : ℕ) := by
  obtain ⟨y, i, h⟩ := exists_two_mul_add (Multiplicative.toAdd m)
  refine ⟨Multiplicative.ofAdd y, i, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, h, nsmul_eq_mul, nsmul_eq_mul,
    mul_one]
  push_cast
  ring

theorem card_sq_eq_one_le_four {c d : ℕ} {G : Type*} [Group G] [Finite G]
    (α : Multiplicative (ZMod c) × Multiplicative (ZMod d) →* G) :
    Nat.card {z : G // z ∈ α.range ∧ z * z = 1} ≤ 4 := by
  set A := α.range with hA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm m m']
  let sq : A →* A :=
    { toFun := fun z => z * z
      map_one' := mul_one 1
      map_mul' := fun x y => Subtype.ext (by
        change (x : G) * y * (x * y) = x * x * (y * y)
        have := hcomm _ x.2 _ y.2
        calc (x : G) * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [this]
          _ = x * x * (y * y) := by group) }
  have h1 := Subgroup.card_ker_mul_card_range sq
  have hker : Nat.card {z : G // z ∈ A ∧ z * z = 1} = Nat.card sq.ker :=
    Nat.card_congr
      { toFun := fun z => ⟨⟨z.1, z.2.1⟩, Subtype.ext z.2.2⟩
        invFun := fun z => ⟨z.1.1, z.1.2, congrArg Subtype.val z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  let e : Fin 2 × Fin 2 → A := fun ij =>
    ⟨α (Multiplicative.ofAdd 1 ^ (ij.1 : ℕ), Multiplicative.ofAdd 1 ^ (ij.2 : ℕ)), ⟨_, rfl⟩⟩
  have hsurj : Function.Surjective (fun w : sq.range × (Fin 2 × Fin 2) => (w.1 : A) * e w.2) := by
    rintro ⟨_, ⟨m₁, m₂⟩, rfl⟩
    obtain ⟨w₁, i, rfl⟩ := exists_sq_mul m₁
    obtain ⟨w₂, j, rfl⟩ := exists_sq_mul m₂
    refine ⟨⟨⟨⟨α (w₁, w₂) * α (w₁, w₂), ⟨(w₁, w₂) * (w₁, w₂), map_mul _ _ _⟩⟩, ?_⟩, (i, j)⟩, ?_⟩
    · exact ⟨⟨α (w₁, w₂), ⟨_, rfl⟩⟩, rfl⟩
    · apply Subtype.ext
      change α (w₁, w₂) * α (w₁, w₂) *
          α (Multiplicative.ofAdd 1 ^ (i : ℕ), Multiplicative.ofAdd 1 ^ (j : ℕ)) =
        α (w₁ ^ 2 * Multiplicative.ofAdd 1 ^ (i : ℕ), w₂ ^ 2 * Multiplicative.ofAdd 1 ^ (j : ℕ))
      rw [← map_mul, ← map_mul]
      congr 1
      ext <;> simp [pow_two]
  have h4 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at h4
  have hpos : 0 < Nat.card sq.range := Nat.card_pos
  rw [hker]
  have h5 : Nat.card sq.ker * Nat.card sq.range ≤ 4 * Nat.card sq.range := by
    rw [h1, Nat.mul_comm 4]
    exact h4
  exact Nat.le_of_mul_le_mul_right h5 hpos

theorem mem_range_inr_of_odd {a b : ℕ} {E : Type*} [Group E] (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b)
    (m : (Multiplicative (ZMod a) × Multiplicative (ZMod b)) × E) (hm : ∃ k : ℕ, m ^ (2 ^ k) = 1) :
    m ∈ (MonoidHom.inr (Multiplicative (ZMod a) × Multiplicative (ZMod b)) E).range := by
  obtain ⟨⟨m₁, m₂⟩, m₃⟩ := m
  obtain ⟨k, hk⟩ := hm
  have h₁ : m₁ ^ (2 ^ k) = 1 := congrArg (fun m => m.1.1) hk
  have h₂ : m₂ ^ (2 ^ k) = 1 := congrArg (fun m => m.1.2) hk
  refine ⟨m₃, ?_⟩
  rw [MonoidHom.inr_apply, eq_one_of_pow_two_pow_zmod ha h₁, eq_one_of_pow_two_pow_zmod hb h₂]
  rfl

theorem mem_range_inl_of_odd {c d : ℕ} {D : Type*} [Group D] (hc : ¬ 2 ∣ c) (hd : ¬ 2 ∣ d)
    (m : D × (Multiplicative (ZMod c) × Multiplicative (ZMod d))) (hm : ∃ k : ℕ, m ^ (2 ^ k) = 1) :
    m ∈ (MonoidHom.inl D (Multiplicative (ZMod c) × Multiplicative (ZMod d))).range := by
  obtain ⟨m₁, ⟨m₂, m₃⟩⟩ := m
  obtain ⟨k, hk⟩ := hm
  have h₂ : m₂ ^ (2 ^ k) = 1 := congrArg (fun m => m.2.1) hk
  have h₃ : m₃ ^ (2 ^ k) = 1 := congrArg (fun m => m.2.2) hk
  refine ⟨m₁, ?_⟩
  rw [MonoidHom.inl_apply, eq_one_of_pow_two_pow_zmod hc h₂, eq_one_of_pow_two_pow_zmod hd h₃]
  rfl

end CFSG.ComponentClassification.Sol76T13.Hq4
