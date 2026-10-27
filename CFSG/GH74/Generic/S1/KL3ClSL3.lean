module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

namespace KL3Z3

def a0 : SL(3, ZMod 3) := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩
def b0 : SL(3, ZMod 3) := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩
def z0 : SL(3, ZMod 3) := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩
def s0 : SL(3, ZMod 3) := ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by decide⟩
def g0 : SL(3, ZMod 3) := ⟨!![0, 0, -1; 1, 0, 1; 0, 1, 0] * !![0, 0, -1; 1, 0, 1; 0, 1, 0], by decide⟩
def h0 : SL(3, ZMod 3) := ⟨!![1, -1, 1; 0, 1, 1; 0, 0, 1], by decide⟩

theorem heis_rel : a0 * b0 = z0 * b0 * a0 := by decide
theorem heis_za : z0 * a0 = a0 * z0 := by decide
theorem heis_zb : z0 * b0 = b0 * z0 := by decide
theorem heis_z3 : z0 ^ 3 = 1 := by decide
theorem heis_zne : z0 ≠ 1 := by decide
theorem heis_s : s0 * z0 = z0 ^ 2 * s0 := by decide
theorem frob_g13 : g0 ^ 13 = 1 := by decide
theorem frob_gne : g0 ≠ 1 := by decide
theorem frob_h : h0 * g0 = g0 ^ 3 * h0 := by decide

end KL3Z3

theorem kl3cl_map_injective {F : Type} [Field F] [CharP F 3] :
    Function.Injective (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 3) F) :
      SL(3, ZMod 3) →* SL(3, F)) := fun _ _ h =>
  Subtype.ext (Matrix.map_injective (ZMod.castHom (dvd_refl 3) F).injective (congrArg Subtype.val h))

theorem kl3cl_charP_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) : CharP F 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (p := 3) (f := 1) (by rw [← Nat.card_eq_fintype_card, hF]; rfl)

theorem kl3cl_heis (F : Type) [Field F] [Finite F] (hF : Nat.card F = 3) :
    ∃ a b z s : SL(3, F), a * b = z * b * a ∧ z * a = a * z ∧ z * b = b * z ∧ z ^ 3 = 1 ∧
      z ≠ 1 ∧ s * z = z ^ 2 * s := by
  have := kl3cl_charP_three hF
  let φ : SL(3, ZMod 3) →* SL(3, F) := Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 3) F)
  refine ⟨φ KL3Z3.a0, φ KL3Z3.b0, φ KL3Z3.z0, φ KL3Z3.s0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, ← map_mul, KL3Z3.heis_rel]
  · rw [← map_mul, ← map_mul, KL3Z3.heis_za]
  · rw [← map_mul, ← map_mul, KL3Z3.heis_zb]
  · rw [← map_pow, KL3Z3.heis_z3, map_one]
  · intro h
    exact KL3Z3.heis_zne (kl3cl_map_injective (F := F) (by rw [h, map_one]))
  · rw [← map_mul, ← map_pow, ← map_mul, KL3Z3.heis_s]

theorem kl3cl_frob (F : Type) [Field F] [Finite F] (hF : Nat.card F = 3) :
    ∃ g h : SL(3, F), g ^ 13 = 1 ∧ g ≠ 1 ∧ h * g = g ^ 3 * h := by
  have := kl3cl_charP_three hF
  let φ : SL(3, ZMod 3) →* SL(3, F) := Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 3) F)
  refine ⟨φ KL3Z3.g0, φ KL3Z3.h0, ?_, ?_, ?_⟩
  · rw [← map_pow, KL3Z3.frob_g13, map_one]
  · intro h
    exact KL3Z3.frob_gne (kl3cl_map_injective (F := F) (by rw [h, map_one]))
  · rw [← map_pow, ← map_mul, ← map_mul, KL3Z3.frob_h]

end CFSG.GH74.Generic.S1
