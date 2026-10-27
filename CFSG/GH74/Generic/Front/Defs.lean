module

public import CFSG.GH74.L5U5.ModelsBasic

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd Subgroup

@[expose] def OddGenerated {Y : Type*} [Group Y] (H : Subgroup Y) : Prop :=
  Subgroup.closure {g : Y | g ∈ H ∧ Odd (orderOf g)} = H

@[expose] def GoodSub (T : Prop) {Y : Type*} [Group Y] (P : Subgroup Y) : Prop :=
  ⁅P, P⁆ = P ∨ (OddGenerated P ∧ T)

@[expose] def ThreeModel (K : Type) [Group K] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ∧
    (Nonempty (K ≃* StatedSL 4 F) ∨ Nonempty (K ≃* StatedSp 2 F))

@[expose] def NoCentral (K : Type) [Group K] : Prop :=
  ∀ ψ : Q8 × Q8 →* K, Function.Injective ψ →
    ψ (QuaternionGroup.a 2, 1) ∉ Subgroup.center K

structure FrontData0 (K : Type) [Group K] where
  φ : Q8 × Q8 →* K
  w : K
  J : Subgroup K
  inj : Function.Injective φ
  w_sq : w * w = 1
  w_swap : ∀ g h : Q8, w * φ (g, h) * w⁻¹ = φ (h, g)
  oneClass : ∀ t : K, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center K →
    ∃ k : K, k * t * k⁻¹ = φ (QuaternionGroup.a 2, 1)
  range_le : φ.range ≤ J
  le_centralizer : J ≤ Subgroup.centralizer ({φ (QuaternionGroup.a 2, 1)} : Set K)
  good : GoodSub (ThreeModel K) J

structure FrontData (K : Type) [Group K] extends FrontData0 K where
  noCentral : NoCentral K

end CFSG.GH74.Generic
