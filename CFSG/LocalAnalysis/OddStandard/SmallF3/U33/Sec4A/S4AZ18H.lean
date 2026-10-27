module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

theorem z18_exp4_aut {Y : Type} [Group Y] [Finite Y] (hcomm : ∀ a b : Y, a * b = b * a)
    (hY2 : ∀ y : Y, y * y = 1) (hcard : Nat.card Y = 16) (σ : MulAut Y)
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1) : σ ^ 4 = 1 := by
  letI : CommGroup Y := { ‹Group Y› with mul_comm := hcomm }
  obtain ⟨k, hk⟩ := hσ
  let V := Additive Y
  have h2 : ∀ x : V, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [two_nsmul, toMul_add, toMul_zero]
    exact hY2 _
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (n := 2) h2
  have hVcard : Nat.card V = 16 := by
    rw [Nat.card_congr Additive.toMul, hcard]
  haveI : Nontrivial V :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hVcard]; norm_num)
  let f : Module.End (ZMod 2) V :=
    AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive σ).toAddMonoidHom
  have hf : ∀ y : Y, f (Additive.ofMul y) = Additive.ofMul (σ y) := fun _ => rfl
  have hpow : ∀ n : ℕ, ∀ y : Y,
      (f ^ n) (Additive.ofMul y) = Additive.ofMul ((σ ^ n) y) := by
    intro n
    induction n with
    | zero => intro y; simp [f]
    | succ n ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, hf, ih, pow_succ, MulAut.mul_apply]
  have hfpow : f ^ (2 ^ k) = 1 := by
    refine LinearMap.ext fun x => ?_
    have h := hpow (2 ^ k) x.toMul
    rw [hk] at h
    simpa using h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (Module.End (ZMod 2) V) 2 :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) (Module.End (ZMod 2) V)) 2 (by norm_num)
  let N : Module.End (ZMod 2) V := f - 1
  have hNnil : IsNilpotent N := by
    refine ⟨2 ^ k, ?_⟩
    have hc : Commute f (1 : Module.End (ZMod 2) V) := Commute.one_right f
    calc N ^ (2 ^ k) = (f - 1) ^ (2 ^ k) := rfl
      _ = f ^ (2 ^ k) - 1 ^ (2 ^ k) := sub_pow_expChar_pow_of_commute 2 k hc
      _ = 1 - 1 := by rw [hfpow, one_pow]
      _ = 0 := sub_self 1
  have hchar : N.charpoly = Polynomial.X ^ Module.finrank (ZMod 2) V :=
    IsNilpotent.charpoly_eq_X_pow_finrank hNnil
  have hrank : Module.finrank (ZMod 2) V = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod, hVcard] at h
    have h' : 2 ^ 4 = 2 ^ Module.finrank (ZMod 2) V := by
      rw [show (2 : ℕ) ^ 4 = 16 from by norm_num]
      exact h
    exact (Nat.pow_right_injective (le_refl 2) h').symm
  have hN4 : N ^ 4 = 0 := by
    have h1 : (Polynomial.aeval N) N.charpoly = 0 := N.aeval_self_charpoly
    rw [hchar, hrank] at h1
    simpa using h1
  have hf4 : f ^ 4 = 1 := by
    have hfN : f = N + 1 := by simp [N]
    rw [hfN]
    have hc : Commute N (1 : Module.End (ZMod 2) V) := Commute.one_right N
    calc (N + 1) ^ 4 = (N + 1) ^ (2 ^ 2) := by norm_num
      _ = N ^ (2 ^ 2) + 1 ^ (2 ^ 2) := add_pow_expChar_pow_of_commute 2 2 hc
      _ = 1 := by
        rw [show (2 : ℕ) ^ 2 = 4 from rfl, hN4, one_pow]
        exact zero_add 1
  refine MulEquiv.ext fun y => ?_
  have h1 := congrArg (fun g : Module.End (ZMod 2) V => g (Additive.ofMul y)) hf4
  simp only [Module.End.one_apply] at h1
  rw [hpow 4 y] at h1
  exact Additive.ofMul.injective h1

end CFSG.OddStandard.SmallF3.HarrisU33.S4A