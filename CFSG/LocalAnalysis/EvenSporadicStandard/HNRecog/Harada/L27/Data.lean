module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup

@[expose] def smallSimpleOrders : List ℕ := [60, 168, 360, 504, 2520, 6048]

@[expose] def SmallSections (X : Type) [Group X] : Prop :=
  ∀ (K : Subgroup X) (L : Subgroup K) [L.Normal], IsSimpleGroup (K ⧸ L) →
    (∃ a b : K ⧸ L, a * b ≠ b * a) →
      Nat.card (K ⧸ L) ∈ smallSimpleOrders ∧
        Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer (K ⧸ L))

structure WrData (X : Type) [Group X] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : X →* (W ≃ₗ[ZMod 2] W)) (w : W) (P F : Subgroup X) (v : X) : Prop where
  ρ_injective : Function.Injective ρ
  finrank_eq : Module.finrank (ZMod 2) W = 8
  card_dvd : Nat.card X ∣ 348364800
  card_le : Nat.card X ≤ 16200
  w_ne_zero : w ≠ 0
  P_fix : ∀ g ∈ P, ρ g w = w
  P_iso : Nonempty (P ≃* Equiv.Perm (Fin 5))
  F_iso : Nonempty (F ≃* alternatingGroup (Fin 5))
  F_fpf : ∀ f ∈ F, orderOf f = 5 → ∀ x : W, ρ f x = x → x = 0
  v_sq : v * v = 1
  v_ne_one : v ≠ 1
  F_comm : ∀ f ∈ F, f * v = v * f
  centralizer_le : ∀ g : X, g * v = v * g → g ∈ F ⊔ Subgroup.zpowers v

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
