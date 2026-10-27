module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

abbrev Z4Z4 : Type := Multiplicative (ZMod 4 × ZMod 4)

abbrev Z8Z8 : Type := Multiplicative (ZMod 8 × ZMod 8)

abbrev E2 (n : ℕ) : Type := Multiplicative (Fin n → ZMod 2)

abbrev Z2xS3 : Type := Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)

@[ext] structure UT3 (R : Type*) [CommRing R] where
  a : R
  b : R
  c : R

namespace UT3

variable {R : Type*} [CommRing R]

instance : Mul (UT3 R) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩⟩

instance : One (UT3 R) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (UT3 R) := ⟨fun x => ⟨-x.a, -x.b, -x.c + x.a * x.b⟩⟩

theorem mul_def (x y : UT3 R) :
    x * y = ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩ := rfl

theorem one_def : (1 : UT3 R) = ⟨0, 0, 0⟩ := rfl

theorem inv_def (x : UT3 R) : x⁻¹ = ⟨-x.a, -x.b, -x.c + x.a * x.b⟩ := rfl

instance : Group (UT3 R) where
  mul_assoc x y z := by
    ext <;> simp only [mul_def] <;> ring
  one_mul x := by
    ext <;> simp only [mul_def, one_def] <;> ring
  mul_one x := by
    ext <;> simp only [mul_def, one_def] <;> ring
  inv_mul_cancel x := by
    ext <;> simp only [mul_def, one_def, inv_def] <;> ring

end UT3

noncomputable abbrev F4 : Type := GaloisField 2 2

noncomputable abbrev F16 : Type := GaloisField 2 4

noncomputable abbrev SylSL3_4 : Type := UT3 F4

noncomputable def bar : F16 →+* F16 := iterateFrobenius F16 2 2

theorem bar_apply (x : F16) : bar x = x ^ 4 := by
  simp [bar, iterateFrobenius_def]

theorem bar_bar (x : F16) : bar (bar x) = x := by
  let _ : Fintype F16 := Fintype.ofFinite F16
  have hc : Fintype.card F16 = 16 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 4 (by norm_num)
  have := FiniteField.pow_card x
  rw [hc] at this
  rw [bar_apply, bar_apply, ← pow_mul]
  exact this

theorem two_eq_zero_F16 : (2 : F16) = 0 := CharP.cast_eq_zero F16 2

@[ext] structure UH where
  a : F16
  b : F16

namespace UH

noncomputable instance : Mul UH := ⟨fun x y => ⟨x.a + y.a, x.b + y.b + x.a * bar y.a⟩⟩

noncomputable instance : One UH := ⟨⟨0, 0⟩⟩

noncomputable instance : Inv UH := ⟨fun x => ⟨-x.a, -x.b + x.a * bar x.a⟩⟩

theorem mul_def (x y : UH) : x * y = ⟨x.a + y.a, x.b + y.b + x.a * bar y.a⟩ := rfl

theorem one_def : (1 : UH) = ⟨0, 0⟩ := rfl

theorem inv_def (x : UH) : x⁻¹ = ⟨-x.a, -x.b + x.a * bar x.a⟩ := rfl

noncomputable instance : Group UH where
  mul_assoc x y z := by
    ext <;> simp only [mul_def, map_add] <;> ring
  one_mul x := by
    ext <;> simp only [mul_def, one_def] <;> ring
  mul_one x := by
    ext <;> simp only [mul_def, one_def, map_zero] <;> ring
  inv_mul_cancel x := by
    ext <;> simp only [mul_def, one_def, inv_def] <;> ring

end UH

noncomputable def sylSU3 : Subgroup UH where
  carrier := {x | x.b + bar x.b + x.a * bar x.a = 0}
  mul_mem' := by
    intro x y hx hy
    change x.b + bar x.b + x.a * bar x.a = 0 at hx
    change y.b + bar y.b + y.a * bar y.a = 0 at hy
    change (x * y).b + bar (x * y).b + (x * y).a * bar (x * y).a = 0
    have h2 := two_eq_zero_F16
    simp only [UH.mul_def, map_add, map_mul, bar_bar]
    linear_combination hx + hy + (x.a * bar y.a + bar x.a * y.a) * h2
  one_mem' := by
    change (1 : UH).b + bar (1 : UH).b + (1 : UH).a * bar (1 : UH).a = 0
    simp [UH.one_def]
  inv_mem' := by
    intro x hx
    change x.b + bar x.b + x.a * bar x.a = 0 at hx
    change (x⁻¹).b + bar (x⁻¹).b + (x⁻¹).a * bar (x⁻¹).a = 0
    have h2 := two_eq_zero_F16
    simp only [UH.inv_def, map_add, map_neg, map_mul, bar_bar]
    linear_combination (-1 : F16) * hx + (2 * x.a * bar x.a) * h2

theorem mem_sylSU3 (x : UH) : x ∈ sylSU3 ↔ x.b + bar x.b + x.a * bar x.a = 0 :=
  ⟨fun h => h, fun h => h⟩

noncomputable abbrev SylSU3_4 : Type := ↥sylSU3

@[expose] def InY (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* E2 4) ∨ Nonempty (T ≃* SylSL3_4) ∨ Nonempty (T ≃* SylSU3_4) ∨
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty (T ≃* Multiplicative (ZMod (2 ^ n) × ZMod (2 ^ n)))

end CFSG.GH74.GLS.Bg.TwoGroups
