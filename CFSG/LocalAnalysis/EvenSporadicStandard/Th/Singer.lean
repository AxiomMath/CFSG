module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Matrix

@[expose] def singerMat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

theorem singerMat_pow_fifteen : singerMat ^ 15 = 1 := by decide

theorem singerMat_mulVec_injective : Function.Injective singerMat.mulVec := by
  intro v w h
  have h15 : singerMat ^ 14 * singerMat = 1 := by
    rw [← pow_succ]
    exact singerMat_pow_fifteen
  have := congrArg (singerMat ^ 14).mulVec h
  rwa [mulVec_mulVec, mulVec_mulVec, h15, one_mulVec, one_mulVec] at this

theorem singerMat_pow_fix (i : ℕ) (hi : ¬ 15 ∣ i) (v : Fin 4 → ZMod 2)
    (hv : (singerMat ^ i).mulVec v = v) : v = 0 := by
  have hmod : singerMat ^ i = singerMat ^ (i % 15) := by
    conv_lhs => rw [← Nat.mod_add_div i 15]
    rw [pow_add, pow_mul, singerMat_pow_fifteen, one_pow, mul_one]
  rw [hmod] at hv
  have hlt : i % 15 < 15 := Nat.mod_lt _ (by norm_num)
  have hne : i % 15 ≠ 0 := fun h => hi (Nat.dvd_of_mod_eq_zero h)
  have key : ∀ j : Fin 15, j ≠ 0 → ∀ v : Fin 4 → ZMod 2,
      (singerMat ^ (j : ℕ)).mulVec v = v → v = 0 := by decide
  exact key ⟨i % 15, hlt⟩ (fun h => hne (congrArg Fin.val h)) v hv

end CFSG.EvenSporadicStandard.ThStd
