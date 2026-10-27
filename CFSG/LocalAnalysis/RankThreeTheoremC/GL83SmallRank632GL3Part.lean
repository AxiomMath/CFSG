module

public import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

private def mulAutLinearEquivTwo {V : Type*} [CommGroup V] [Module (ZMod 2) (Additive V)]
    (α : MulAut V) : Additive V ≃ₗ[ZMod 2] Additive V :=
  (MulEquiv.toAdditive α).toLinearEquiv fun c x => by
    simpa using ZMod.map_smul (MulEquiv.toAdditive α).toAddMonoidHom c x

private def mulAutToLinearEquivTwo (V : Type*) [CommGroup V] [Module (ZMod 2) (Additive V)] :
    MulAut V →* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun := mulAutLinearEquivTwo
  map_one' := LinearEquiv.ext fun _ => Additive.toMul.injective rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Additive.toMul.injective rfl

private theorem mulAutToLinearEquivTwo_injective (V : Type*) [CommGroup V]
    [Module (ZMod 2) (Additive V)] : Function.Injective (mulAutToLinearEquivTwo V) := by
  intro α β h
  ext v
  exact congrArg (fun e => Additive.toMul (e (Additive.ofMul v))) h

private theorem card_dvd_card_GL {V : Type*} [CommGroup V] [Finite V]
    [Module (ZMod 2) (Additive V)] {Γ : Type*} [Group Γ] (ρ : Γ →* MulAut V)
    (hρ : Function.Injective ρ) :
    Nat.card Γ ∣ Nat.card (GL (Fin (Module.finrank (ZMod 2) (Additive V))) (ZMod 2)) := by
  classical
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) (Additive V)
  let ψ : (Additive V ≃ₗ[ZMod 2] Additive V) ≃* GL (Fin (Module.finrank (ZMod 2) (Additive V)))
      (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm
  exact Subgroup.card_dvd_of_injective (ψ.toMonoidHom.comp ((mulAutToLinearEquivTwo V).comp ρ))
    (ψ.injective.comp ((mulAutToLinearEquivTwo_injective V).comp hρ))

private theorem not_dvd_card_GL_two (d : ℕ) (hd : d ≤ 6) :
    ¬ 3 ^ 5 ∣ ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  interval_cases d <;> simp [Fin.prod_univ_succ]

private theorem card_dvd_eighty_one_aux {V : Type*} [CommGroup V] [Finite V]
    (hV2 : ∀ a : V, a ^ 2 = 1) (hVc : Nat.card V ≤ 2 ^ 6)
    {Γ : Type*} [Group Γ] [Finite Γ] (hΓ : IsPGroup 3 Γ) (ρ : Γ →* MulAut V)
    (hρ : Function.Injective ρ) : Nat.card Γ ∣ 81 := by
  have h2 : ∀ x : Additive V, 2 • x = 0 := fun x =>
    Additive.toMul.injective (by simpa using hV2 (Additive.toMul x))
  let : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hdim : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rwa [Nat.card_zmod] at this
  have hd : Module.finrank (ZMod 2) (Additive V) ≤ 6 := by
    rw [hdim] at hVc
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hVc
  obtain ⟨k, hk⟩ := hΓ.exists_card_eq
  have hdvd := card_dvd_card_GL ρ hρ
  rw [Matrix.card_GL_field, ZMod.card, hk] at hdvd
  have hk5 : k < 5 := by
    by_contra hk5
    exact not_dvd_card_GL_two _ hd ((pow_dvd_pow 3 (not_lt.1 hk5)).trans hdvd)
  rw [hk]
  exact (pow_dvd_pow 3 (by omega : k ≤ 4)).trans (by norm_num)

theorem card_dvd_eighty_one_of_faithful_action {V : Type*} [Group V] [Finite V]
    (hV : ∀ a b : V, a * b = b * a) (hV2 : ∀ a : V, a ^ 2 = 1) (hVc : Nat.card V ≤ 2 ^ 6)
    {Γ : Type*} [Group Γ] [Finite Γ] (hΓ : IsPGroup 3 Γ) (ρ : Γ →* MulAut V)
    (hρ : Function.Injective ρ) : Nat.card Γ ∣ 81 := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hV }
  exact card_dvd_eighty_one_aux hV2 hVc hΓ ρ hρ

end CFSG.LocalAnalysis.RankThreeTheoremC
