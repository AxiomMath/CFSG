module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.HardMathSupport.U4FF

theorem card_linearEquiv_eq_prod {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {n : ℕ} (hn : Module.finrank (ZMod 2) V = n) :
    Nat.card (V ≃ₗ[ZMod 2] V) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  let b : Module.Basis (Fin n) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V hn
  let e : GL (Fin n) (ZMod 2) ≃* (V ≃ₗ[ZMod 2] V) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card]

theorem prod_pow_sub_le_of_le_four (d : ℕ) (hd : d ≤ 4) :
    ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) ≤ 20160 := by
  interval_cases d <;> simp [Fin.prod_univ_succ]

theorem card_le_of_faithful_finrank_le_four {G W : Type} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : G →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ)
    (hW : Module.finrank (ZMod 2) W ≤ 4) : Nat.card G ≤ 20160 := by
  haveI : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W)) LinearEquiv.coe_injective
  have h1 : Nat.card G ≤ Nat.card (W ≃ₗ[ZMod 2] W) :=
    Nat.card_le_card_of_injective (ρ : G → (W ≃ₗ[ZMod 2] W)) hρ
  rw [card_linearEquiv_eq_prod (n := Module.finrank (ZMod 2) W) rfl] at h1
  exact h1.trans (prod_pow_sub_le_of_le_four _ hW)

end CFSG.HardMathSupport.U4FF
