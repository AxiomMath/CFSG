module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

open Polynomial in
theorem geom_sum_eq_sub_one_pow (p : ℕ) [hp : Fact p.Prime] {R : Type*} [Ring R]
    [Algebra (ZMod p) R] (β : R) (r : ℕ) :
    ∑ k ∈ Finset.range (p ^ r), β ^ k = (β - 1) ^ (p ^ r - 1) := by
  have hn : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp.out.pos
  have key : (∑ k ∈ Finset.range (p ^ r), (X : (ZMod p)[X]) ^ k) = (X - 1) ^ (p ^ r - 1) := by
    have hne : (X - 1 : (ZMod p)[X]) ≠ 0 := by
      have := X_sub_C_ne_zero (1 : ZMod p)
      rwa [map_one] at this
    apply mul_left_cancel₀ hne
    rw [mul_geom_sum, ← pow_succ', Nat.sub_add_cancel hn, sub_pow_char_pow, one_pow]
  have := congrArg (aeval β) key
  simpa [map_sum] using this

theorem prod_iterate_eq_one_aux {Y : Type*} [CommGroup Y] (p : ℕ) [hp : Fact p.Prime]
    [Module (ZMod p) (Additive Y)] (α β : Y →* Y) (hαβ : ∀ y, α (β y) = y)
    (hβα : ∀ y, β (α y) = y) (hnil : ∀ y, (fun z => z * (α z)⁻¹)^[p - 1] y = 1) {r : ℕ}
    (hr : 1 ≤ r) (h : Y) : ∏ k ∈ Finset.range (p ^ r), β^[k] h = 1 := by
  let A : Module.End (ZMod p) (Additive Y) := (MonoidHom.toAdditive α).toZModLinearMap p
  let B : Module.End (ZMod p) (Additive Y) := (MonoidHom.toAdditive β).toZModLinearMap p
  have hA : ∀ y : Y, A (Additive.ofMul y) = Additive.ofMul (α y) := fun _ => rfl
  have hB : ∀ y : Y, B (Additive.ofMul y) = Additive.ofMul (β y) := fun _ => rfl
  have hBA : B * A = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, ← ofMul_toMul x, hA, hB, hβα]
    rfl
  have hAB : A * B = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, ← ofMul_toMul x, hB, hA, hαβ]
    rfl
  have hD : ∀ (n : ℕ) (y : Y), ((1 - A) ^ n) (Additive.ofMul y) =
      Additive.ofMul ((fun z => z * (α z)⁻¹)^[n] y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply', LinearMap.sub_apply,
        Module.End.one_apply, hA, ofMul_mul, ofMul_inv, sub_eq_add_neg]
  have hDp : (1 - A) ^ (p - 1) = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [← ofMul_toMul x, hD, hnil]
    rfl
  have hcomm : Commute B (1 - A) := by
    show B * (1 - A) = (1 - A) * B
    rw [mul_sub, sub_mul, mul_one, one_mul, hBA, hAB]
  have hB1 : B - 1 = B * (1 - A) := by rw [mul_sub, mul_one, hBA]
  have hBnil : (B - 1) ^ (p - 1) = 0 := by rw [hB1, hcomm.mul_pow, hDp, mul_zero]
  have hsum : ∑ k ∈ Finset.range (p ^ r), B ^ k = 0 := by
    rw [geom_sum_eq_sub_one_pow p B r]
    have hpr : p ≤ p ^ r := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ r := Nat.pow_le_pow_right hp.out.pos hr
    have e : p ^ r - 1 = (p - 1) + (p ^ r - p) := by
      have := hp.out.one_lt
      omega
    rw [e, pow_add, hBnil, zero_mul]
  have hiter : ∀ (k : ℕ) (y : Y), (B ^ k) (Additive.ofMul y) = Additive.ofMul (β^[k] y) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply, ih, hB, Function.iterate_succ_apply']
  have h0 := congrArg (fun F : Module.End (ZMod p) (Additive Y) => F (Additive.ofMul h)) hsum
  rw [LinearMap.sum_apply] at h0
  simp only [hiter, LinearMap.zero_apply] at h0
  apply Additive.ofMul.injective
  rw [ofMul_prod, ofMul_one]
  exact h0

theorem prod_iterate_eq_one {Y : Type*} [CommGroup Y] (p : ℕ) [hp : Fact p.Prime]
    (hY : ∀ y : Y, y ^ p = 1) (α β : Y →* Y) (hαβ : ∀ y, α (β y) = y) (hβα : ∀ y, β (α y) = y)
    (hnil : ∀ y, (fun z => z * (α z)⁻¹)^[p - 1] y = 1) {r : ℕ} (hr : 1 ≤ r) (h : Y) :
    ∏ k ∈ Finset.range (p ^ r), β^[k] h = 1 := by
  have hexp : ∀ x : Additive Y, p • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero, hY]
  letI : Module (ZMod p) (Additive Y) := AddCommGroup.zmodModule hexp
  exact prod_iterate_eq_one_aux p α β hαβ hβα hnil hr h

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

end
