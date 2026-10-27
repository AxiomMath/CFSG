module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private theorem fx_three_nsmul (v : V) : (3 : ℕ) • v = 0 := by
  have h : ((3 : ℕ) : ZMod 3) = 0 := by decide
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3), h, zero_smul]

theorem fx_one_add_pow_three (M : Module.End (ZMod 3) V) : (1 + M) ^ 3 = 1 + M ^ 3 := by
  have h3M : ∀ P : Module.End (ZMod 3) V, (3 : ℕ) • P = 0 := fun P => by
    ext v
    simp [fx_three_nsmul]
  have h : (1 + M) ^ 3 = 1 + (3 : ℕ) • M + (3 : ℕ) • M ^ 2 + M ^ 3 := by noncomm_ring
  rw [h, h3M M, h3M (M ^ 2)]
  simp

theorem fx_sub_one_pow_three (U : Module.End (ZMod 3) V) : (U - 1) ^ 3 = U ^ 3 - 1 := by
  have h := fx_one_add_pow_three (U - 1)
  rw [add_sub_cancel] at h
  rw [h]
  abel

theorem fx_sub_one_pow_nine (U : Module.End (ZMod 3) V) (hU : U ^ 9 = 1) : (U - 1) ^ 9 = 0 := by
  calc (U - 1) ^ 9 = ((U - 1) ^ 3) ^ 3 := by rw [← pow_mul]
    _ = (U ^ 3 - 1) ^ 3 := by rw [fx_sub_one_pow_three]
    _ = (U ^ 3) ^ 3 - 1 := fx_sub_one_pow_three (U ^ 3)
    _ = U ^ 9 - 1 := by rw [← pow_mul]
    _ = 0 := by rw [hU]; simp

theorem fx_pow_finrank_apply_eq_zero [FiniteDimensional (ZMod 3) V] (N : Module.End (ZMod 3) V)
    {m : ℕ} (hN : N ^ m = 0) {W : Submodule (ZMod 3) V} (hW : ∀ w ∈ W, N w ∈ W) {w : V}
    (hw : w ∈ W) : (N ^ Module.finrank (ZMod 3) W) w = 0 := by
  set f : Module.End (ZMod 3) W := N.restrict hW with hfdef
  have hpow : ∀ n : ℕ, ∀ x : W, ((f ^ n) x : V) = (N ^ n) (x : V) := fun n x => by
    rw [hfdef, Module.End.pow_restrict n hW]
    rfl
  have hf : f ^ (m + Module.finrank (ZMod 3) W) = 0 := by
    ext x
    rw [LinearMap.zero_apply, Submodule.coe_zero, hpow, pow_add, Module.End.mul_apply, hN]
    simp
  have hker : LinearMap.ker (f ^ (m + Module.finrank (ZMod 3) W)) =
      LinearMap.ker (f ^ Module.finrank (ZMod 3) W) :=
    Module.End.ker_pow_eq_ker_pow_finrank_of_le (Nat.le_add_left _ _)
  have h2 : f ^ Module.finrank (ZMod 3) W = 0 := by
    have h3 : LinearMap.ker (f ^ Module.finrank (ZMod 3) W) = ⊤ := by
      rw [← hker, hf]
      exact LinearMap.ker_zero
    exact LinearMap.ker_eq_top.mp h3
  have h4 := congrArg (fun F : Module.End (ZMod 3) W => ((F ⟨w, hw⟩ : W) : V)) h2
  simpa [hpow] using h4

end CFSG.OddStandard.SmallF3.Omega
