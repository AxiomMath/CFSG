module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def Sylow2In (P H : Subgroup G) : Prop :=
  P ≤ H ∧ IsPGroup 2 ↥P ∧ ¬ 2 ∣ P.relIndex H

@[expose] def IsElemAb2 (E : Subgroup G) : Prop :=
  ∀ a ∈ E, a * a = 1 ∧ ∀ b ∈ E, a * b = b * a

@[expose] def IsFourGroup (V : Subgroup G) : Prop := IsElemAb2 V ∧ Nat.card V = 4

@[expose] def Rank2LE (H : Subgroup G) (n : ℕ) : Prop :=
  ∀ E : Subgroup G, E ≤ H → IsElemAb2 E → Nat.card E ≤ 2 ^ n

@[expose] def Is3Element (f : G) : Prop := ∃ k : ℕ, f ^ 3 ^ k = 1

abbrev E24 : Type := Fin 4 → Multiplicative (ZMod 2)

abbrev Z2n2 (n : ℕ) : Type := Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))

@[ext] structure UT3 (F : Type*) [CommRing F] where
  a : F
  b : F
  c : F

namespace UT3

variable {F : Type*} [CommRing F]

instance : Mul (UT3 F) := ⟨fun u v => ⟨u.a + v.a, u.b + v.b, u.c + v.c + u.a * v.b⟩⟩
instance : One (UT3 F) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (UT3 F) := ⟨fun u => ⟨-u.a, -u.b, -u.c + u.a * u.b⟩⟩

@[simp] theorem mul_a (u v : UT3 F) : (u * v).a = u.a + v.a := rfl
@[simp] theorem mul_b (u v : UT3 F) : (u * v).b = u.b + v.b := rfl
@[simp] theorem mul_c (u v : UT3 F) : (u * v).c = u.c + v.c + u.a * v.b := rfl
@[simp] theorem one_a : (1 : UT3 F).a = 0 := rfl
@[simp] theorem one_b : (1 : UT3 F).b = 0 := rfl
@[simp] theorem one_c : (1 : UT3 F).c = 0 := rfl
@[simp] theorem inv_a (u : UT3 F) : (u⁻¹).a = -u.a := rfl
@[simp] theorem inv_b (u : UT3 F) : (u⁻¹).b = -u.b := rfl
@[simp] theorem inv_c (u : UT3 F) : (u⁻¹).c = -u.c + u.a * u.b := rfl

instance : Group (UT3 F) where
  mul_assoc u v w := by ext <;> simp <;> ring
  one_mul u := by ext <;> simp
  mul_one u := by ext <;> simp
  inv_mul_cancel u := by ext <;> simp

end UT3

theorem gf16_char2 : (2 : GaloisField 2 4) = 0 := by
  have : ((2 : ℕ) : GaloisField 2 4) = 0 := CharP.cast_eq_zero (GaloisField 2 4) 2
  simpa using this

theorem gf16_add_pow4 (a b : GaloisField 2 4) : (a + b) ^ 4 = a ^ 4 + b ^ 4 := by
  have := add_pow_char_pow (R := GaloisField 2 4) (p := 2) (n := 2) a b
  simpa using this

theorem gf16_pow16 (a : GaloisField 2 4) : a ^ 16 = a := by
  have : Fintype (GaloisField 2 4) := Fintype.ofFinite _
  have h := FiniteField.pow_card a
  have hc : Fintype.card (GaloisField 2 4) = 2 ^ 4 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 4 (by norm_num)
  rw [hc] at h
  simpa using h

@[expose] def SylSU34 : Subgroup (UT3 (GaloisField 2 4)) where
  carrier := {u | u.b = u.a ^ 4 ∧ u.c + u.c ^ 4 + u.a * u.a ^ 4 = 0}
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨?_, ?_⟩
    · show u.b + v.b = (u.a + v.a) ^ 4
      rw [gf16_add_pow4, hu1, hv1]
    · show (u.c + v.c + u.a * v.b) + (u.c + v.c + u.a * v.b) ^ 4 +
        (u.a + v.a) * (u.a + v.a) ^ 4 = 0
      have e1 : (u.c + v.c + u.a * v.b) ^ 4 = u.c ^ 4 + v.c ^ 4 + u.a ^ 4 * v.a := by
        rw [gf16_add_pow4, gf16_add_pow4, hv1]
        have h16 := gf16_pow16 v.a
        calc u.c ^ 4 + v.c ^ 4 + (u.a * v.a ^ 4) ^ 4 = u.c ^ 4 + v.c ^ 4 + u.a ^ 4 * v.a ^ 16 := by
              ring
          _ = _ := by rw [h16]
      rw [e1, gf16_add_pow4, hv1]
      linear_combination hu2 + hv2 + (u.a * v.a ^ 4 + u.a ^ 4 * v.a) * gf16_char2
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    refine ⟨?_, ?_⟩
    · show -u.b = (-u.a) ^ 4
      rw [hu1]
      have : (-u.a) ^ 4 = u.a ^ 4 := by ring
      rw [this]
      linear_combination (-u.a ^ 4) * gf16_char2
    · show (-u.c + u.a * u.b) + (-u.c + u.a * u.b) ^ 4 + (-u.a) * (-u.a) ^ 4 = 0
      have e1 : (-u.c + u.a * u.b) ^ 4 = u.c ^ 4 + u.a ^ 4 * u.a := by
        rw [gf16_add_pow4, hu1]
        have h16 := gf16_pow16 u.a
        calc (-u.c) ^ 4 + (u.a * u.a ^ 4) ^ 4 = u.c ^ 4 + u.a ^ 4 * u.a ^ 16 := by ring
          _ = _ := by rw [h16]
      rw [e1, hu1]
      linear_combination hu2 + (-u.c) * gf16_char2

theorem mem_SylSU34_iff (u : UT3 (GaloisField 2 4)) :
    u ∈ SylSU34 ↔ u.b = u.a ^ 4 ∧ u.c + u.c ^ 4 + u.a * u.a ^ 4 = 0 := Iff.rfl

@[expose] def Hzero (H : Subgroup G) (f : G) : Subgroup G := ⁅H, zpowers f⁆

@[expose] def IsYGroup (P : Type*) [Group P] : Prop :=
  Nonempty (P ≃* E24) ∨ Nonempty (P ≃* UT3 (GaloisField 2 2)) ∨ Nonempty (P ≃* ↥SylSU34) ∨
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty (P ≃* Z2n2 n)

@[expose] def sq (H : Subgroup G) : Subgroup G := Subgroup.closure {z | ∃ h ∈ H, z = h * h}

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

