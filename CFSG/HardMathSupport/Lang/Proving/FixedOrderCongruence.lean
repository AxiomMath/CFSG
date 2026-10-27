module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.HardMathSupport.Lang.Proving

theorem card_modEq_card_fixedPoints_of_pow_prime {K : Type*} [Group K] [Finite K]
    (α : MulAut K) {p : ℕ} [hp : Fact p.Prime] (hα : α ^ p = 1) :
    Nat.card K ≡ Nat.card {x : K // α x = x} [MOD p] := by
  classical
  have hfin : Fintype K := Fintype.ofFinite K
  let f : Function.End K := fun x => α x
  have hpow : ∀ (n : ℕ) (x : K), (f ^ n) x = (α ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, MulAut.mul_apply]
      exact ih (α x)
  have hf : f ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext x
    rw [hpow p x, hα]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) (f := f) hf
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hmod

end CFSG.HardMathSupport.Lang.Proving
