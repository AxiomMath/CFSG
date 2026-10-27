module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Stab
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem vec_add_self_aux (a : ZMod 2) (v : V) : a • v + a • v = 0 := by
  rw [← add_smul, zmod_two_add_self, zero_smul]

@[expose] def tvec (v : V) (f : V →ₗ[ZMod 2] ZMod 2) (hf : f v = 0) : V ≃ₗ[ZMod 2] V where
  toFun u := u + f u • v
  invFun u := u + f u • v
  map_add' x y := by simp only [map_add, add_smul]; abel
  map_smul' c x := by simp [smul_add, smul_smul]
  left_inv u := by
    simp only [map_add, map_smul, hf, mul_zero, add_zero, smul_eq_mul]
    rw [add_assoc, vec_add_self_aux, add_zero]
  right_inv u := by
    simp only [map_add, map_smul, hf, mul_zero, add_zero, smul_eq_mul]
    rw [add_assoc, vec_add_self_aux, add_zero]

theorem tvec_apply (v : V) (f : V →ₗ[ZMod 2] ZMod 2) (hf : f v = 0) (u : V) :
    tvec v f hf u = u + f u • v := rfl

theorem orderOf_tvec_mul (v w : V) (f g : V →ₗ[ZMod 2] ZMod 2) (hfv : f v = 0) (hgw : g w = 0)
    (hfw : f w = 1) (hgv : g v = 1) :
    orderOf (tvec v f hfv * tvec w g hgw) = 3 := by
  have hvw : w ≠ v := by
    intro h; rw [h] at hfw; rw [hfv] at hfw; exact absurd hfw (by decide)
  have key : (tvec v f hfv * tvec w g hgw) ^ 3 = 1 := by
    apply LinearEquiv.ext
    intro u
    change ((tvec v f hfv * tvec w g hgw) ^ 3) u = u
    simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply, tvec_apply, map_add, map_smul,
      hfv, hgw, hfw, hgv]
    match_scalars <;> (generalize f u = p; generalize g u = q; revert p q; decide)
  have hne : tvec v f hfv * tvec w g hgw ≠ 1 := by
    intro h
    have := congrArg (fun a : V ≃ₗ[ZMod 2] V => a v) h
    have e : (tvec v f hfv * tvec w g hgw) v = w := by
      simp only [LinearEquiv.mul_apply, tvec_apply, map_add, map_smul, smul_eq_mul, hfv, hgw, hfw,
        hgv]
      match_scalars <;> decide
    change (tvec v f hfv * tvec w g hgw) v = v at this
    rw [e] at this
    exact hvw this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime key hne

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
