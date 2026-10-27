module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.U4FF

variable {F : Type} [Field F] [Finite F] {k : Type*} [Field k] [Algebra F k]

theorem exists_char_exponent (c : Fˣ → k) (hmul : ∀ r r', c (r * r') = c r * c r')
    (hone : c 1 = 1) :
    ∃ e < Nat.card Fˣ, ∀ r : Fˣ, c r = algebraMap F k (r : F) ^ e := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hN : 0 < Nat.card Fˣ := Nat.card_pos
  have hprim : IsPrimitiveRoot (algebraMap F k (g : F)) (Nat.card Fˣ) := by
    have h1 : IsPrimitiveRoot (g : F) (Nat.card Fˣ) := by
      rw [← hord, ← orderOf_units]
      exact IsPrimitiveRoot.orderOf _
    exact h1.map_of_injective (algebraMap F k).injective
  have hpow : ∀ (r : Fˣ) (n : ℕ), c (r ^ n) = c r ^ n := by
    intro r n
    induction n with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hcN : c g ^ Nat.card Fˣ = 1 := by rw [← hpow, pow_card_eq_one', hone]
  obtain ⟨e, heN, he⟩ := hprim.eq_pow_of_pow_eq_one hcN
  refine ⟨e, heN, fun r => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, g ^ j = r :=
    (mem_powers_iff_mem_zpowers.mpr (hg r))
  rw [hpow, ← he, ← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val, map_pow]

theorem units_pow_eq_one_iff (e : ℕ) :
    (∀ r : Fˣ, algebraMap F k (r : F) ^ e = 1) ↔ Nat.card Fˣ ∣ e := by
  classical
  constructor
  · intro h
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    have hprim : IsPrimitiveRoot (algebraMap F k (g : F)) (Nat.card Fˣ) := by
      have h1 : IsPrimitiveRoot (g : F) (Nat.card Fˣ) := by
        rw [← hord, ← orderOf_units]
        exact IsPrimitiveRoot.orderOf _
      exact h1.map_of_injective (algebraMap F k).injective
    exact hprim.dvd_of_pow_eq_one e (h g)
  · rintro ⟨m, rfl⟩ r
    have h1 : (algebraMap F k (r : F)) ^ Nat.card Fˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
    rw [pow_mul, h1, one_pow]

end CFSG.HardMathSupport.U4FF
