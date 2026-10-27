module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem additive_two_nsmul_eq_zero (hV2 : ∀ v : V, v * v = 1) (x : Additive V) :
    (2 : ℕ) • x = 0 := by
  rw [two_nsmul]
  show (x + x).toMul = (0 : Additive V).toMul
  rw [toMul_add, toMul_zero]
  exact hV2 x.toMul

theorem card_mulAut_elemAb_two (hV2 : ∀ v : V, v * v = 1) {k : ℕ} (hV : Nat.card V = 2 ^ k) :
    Nat.card (MulAut V) = ∏ i ∈ Finset.range k, (2 ^ k - 2 ^ i) := by
  let _ : Module (ZMod 2) (Additive V) :=
    AddCommGroup.zmodModule (additive_two_nsmul_eq_zero hV2)
  have hfin : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) (Additive V) = k := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have h2 : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
    rw [h2, hV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hrank
  let e1 : MulAut V ≃ (Additive V ≃ₗ[ZMod 2] Additive V) :=
    { toFun := fun σ => (MulEquiv.toAdditive σ).toLinearEquiv
        (fun c x => ZMod.map_smul (MulEquiv.toAdditive σ) c x)
      invFun := fun e => MulEquiv.toAdditive.symm e.toAddEquiv
      left_inv := fun σ => by ext; rfl
      right_inv := fun e => by ext; rfl }
  let e2 : Matrix.GeneralLinearGroup (Fin k) (ZMod 2) ≃* (Additive V ≃ₗ[ZMod 2] Additive V) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive V))
  rw [Nat.card_congr e1, ← Nat.card_congr e2.toEquiv, Matrix.card_GL_field]
  rw [ZMod.card, Fin.prod_univ_eq_prod_range (fun i => 2 ^ k - 2 ^ i) k]

theorem not_dvd_27_of_small (hV2 : ∀ v : V, v * v = 1) {k : ℕ} (hk : k ≤ 5)
    (hV : Nat.card V = 2 ^ k) {H : Type*} [Group H] [Finite H] (f : H →* MulAut V)
    (hf : Function.Injective f) : ¬ 27 ∣ Nat.card H := by
  intro h27
  have hdvd : Nat.card H ∣ Nat.card (MulAut V) := Subgroup.card_dvd_of_injective f hf
  rw [card_mulAut_elemAb_two hV2 hV] at hdvd
  have h := h27.trans hdvd
  interval_cases k <;> simp [Finset.prod_range_succ] at h

theorem not_dvd_25_of_six (hV2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 2 ^ 6)
    {H : Type*} [Group H] [Finite H] (f : H →* MulAut V) (hf : Function.Injective f) :
    ¬ 25 ∣ Nat.card H := by
  intro h25
  have hdvd : Nat.card H ∣ Nat.card (MulAut V) := Subgroup.card_dvd_of_injective f hf
  rw [card_mulAut_elemAb_two hV2 hV] at hdvd
  have h := h25.trans hdvd
  simp [Finset.prod_range_succ] at h

end CFSG.EvenSporadicStandard.M24Std.DResH
