module

public import CFSG.HardMathSupport.Lang.Proving.CubeClassCyclic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Lang.Proving

theorem exists_cube_iff_pow_eq_one {K : Type*} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) (x : Kˣ) :
    (∃ y : Kˣ, y ^ 3 = x) ↔ x ^ ((Nat.card K - 1) / 3) = 1 := by
  have hcard : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have h3' : 3 ∣ Nat.card Kˣ := hcard ▸ h3
  have key := mem_range_pow_three_iff h3' x
  rw [hcard] at key
  constructor
  · rintro ⟨y, rfl⟩
    exact (key.mp ⟨y, rfl⟩)
  · intro hx
    obtain ⟨y, hy⟩ := key.mpr hx
    exact ⟨y, by simpa [powMonoidHom_apply] using hy⟩

end CFSG.HardMathSupport.Lang.Proving

end
