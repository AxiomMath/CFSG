module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix

theorem n24_rank_three (τ x : GL (Fin 6) (ZMod 2)) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hxτ : x * τ = τ * x) (hx7 : x ^ 7 = 1)
    (hxf : ∀ v : Fin 6 → ZMod 2, (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v → v = 0) :
    Module.finrank (ZMod 2)
      (LinearMap.range (Matrix.toLin' ((τ : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1))) = 3 := by
  classical
  have h2z : ∀ a : ZMod 2, a + a = 0 := by decide
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin 6) (Fin 6) (ZMod 2),
      T = (τ : Matrix (Fin 6) (Fin 6) (ZMod 2)) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 6) (Fin 6) (ZMod 2),
      X = (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) := ⟨_, rfl⟩
  rw [← hT]
  have hTT : T * T = 1 := by
    have h := congrArg (fun u : GL (Fin 6) (ZMod 2) => (u : Matrix (Fin 6) (Fin 6) (ZMod 2))) hτ
    simpa [hT] using h
  have hXT : X * T = T * X := by
    have h := congrArg (fun u : GL (Fin 6) (ZMod 2) => (u : Matrix (Fin 6) (Fin 6) (ZMod 2))) hxτ
    simpa [hT, hX] using h
  have hX7 : X ^ 7 = 1 := by
    have h := congrArg (fun u : GL (Fin 6) (ZMod 2) => (u : Matrix (Fin 6) (Fin 6) (ZMod 2))) hx7
    simpa [hX] using h
  have hXf : ∀ v : Fin 6 → ZMod 2, X *ᵥ v = v → v = 0 := by
    intro v hv
    exact hxf v (by rw [← hX]; exact hv)
  have hT1 : T ≠ 1 := by
    intro h
    apply hτ1
    exact Units.ext (by rw [← hT]; exact h)
  have h2 : ∀ M : Matrix (Fin 6) (Fin 6) (ZMod 2), M + M = 0 := by
    intro M
    exact Matrix.ext fun i j => h2z (M i j)
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 6) (Fin 6) (ZMod 2), N = T + 1 := ⟨_, rfl⟩
  rw [← hN]
  have hNN : N * N = 0 := by
    have e : N * N = (T * T + 1) + (T + T) := by
      rw [hN]
      simp only [add_mul, mul_add, mul_one, one_mul]
      abel
    rw [e, hTT, h2 T, add_zero, h2 1]
  have hXN : X * N = N * X := by
    rw [hN, mul_add, add_mul, mul_one, one_mul, hXT]
  obtain ⟨L, hL⟩ : ∃ L : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2), L = Matrix.toLin' N :=
    ⟨_, rfl⟩
  rw [← hL]
  have hLapp : ∀ v, L v = N *ᵥ v := by
    intro v
    rw [hL, Matrix.toLin'_apply]
  have hLL : ∀ v, L (L v) = 0 := by
    intro v
    rw [hLapp, hLapp, Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  have hrk : Module.finrank (ZMod 2) (LinearMap.range L) +
      Module.finrank (ZMod 2) (LinearMap.ker L) = 6 := by
    rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]
  have hle : LinearMap.range L ≤ LinearMap.ker L := by
    rintro _ ⟨v, rfl⟩
    exact hLL v
  have hmono := Submodule.finrank_mono hle
  have hr3 : Module.finrank (ZMod 2) (LinearMap.range L) ≤ 3 := by omega
  have hr1 : 1 ≤ Module.finrank (ZMod 2) (LinearMap.range L) := by
    by_contra hlt
    have h0 : Module.finrank (ZMod 2) (LinearMap.range L) = 0 := by omega
    have hbot : LinearMap.range L = ⊥ := Submodule.finrank_eq_zero.1 h0
    have hL0 : L = 0 := LinearMap.range_eq_bot.1 hbot
    have hN0 : N = 0 := by
      apply Matrix.toLin'.injective
      rw [← hL, hL0, map_zero]
    apply hT1
    have : T + 1 + 1 = T := by rw [add_assoc, h2 1, add_zero]
    rw [← this, ← hN, hN0, zero_add]
  obtain ⟨W, hW⟩ : ∃ W : Submodule (ZMod 2) (Fin 6 → ZMod 2), W = LinearMap.range L := ⟨_, rfl⟩
  rw [← hW] at hr3 hr1 ⊢
  have hWX : ∀ w ∈ W, X *ᵥ w ∈ W := by
    intro w hw
    rw [hW] at hw ⊢
    obtain ⟨u, rfl⟩ := hw
    refine ⟨X *ᵥ u, ?_⟩
    rw [hLapp, hLapp, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hXN]
  haveI : Fintype W := Fintype.ofFinite W
  let f : Function.End W := fun w => ⟨X *ᵥ w.1, hWX w.1 w.2⟩
  have hfpow : ∀ (n : ℕ) (w : W),
      ((f ^ n) w : Fin 6 → ZMod 2) = (X ^ n) *ᵥ (w : Fin 6 → ZMod 2) := by
    intro n
    induction n with
    | zero =>
      intro w
      rw [pow_zero, pow_zero, Matrix.one_mulVec]
      rfl
    | succ n ih =>
      intro w
      have e : (f ^ (n + 1)) w = (f ^ n) (f w) := by rw [pow_succ]; rfl
      rw [e, ih, show ((f w : W) : Fin 6 → ZMod 2) = X *ᵥ (w : Fin 6 → ZMod 2) from rfl,
        Matrix.mulVec_mulVec, ← pow_succ]
  have hf : f ^ 7 ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    rw [pow_one, hfpow, hX7, Matrix.one_mulVec]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 7) (n := 1) (α := W) (f := f) hf
  have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨0, W.zero_mem⟩, ?_⟩, ?_⟩
    · apply Subtype.ext
      show X *ᵥ (0 : Fin 6 → ZMod 2) = 0
      exact Matrix.mulVec_zero X
    · rintro ⟨w, hw⟩
      have hfw : f w = w := hw
      have h0 : (w : Fin 6 → ZMod 2) = 0 := by
        apply hXf
        exact congrArg Subtype.val hfw
      apply Subtype.ext
      apply Subtype.ext
      exact h0
  have hcard : Fintype.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hfix, hcard] at hmod
  generalize Module.finrank (ZMod 2) W = r at hr1 hr3 hmod ⊢
  interval_cases r <;> simp [Nat.ModEq] at hmod ⊢

end CFSG.OddStandard.HigherRank.YamadaG23
