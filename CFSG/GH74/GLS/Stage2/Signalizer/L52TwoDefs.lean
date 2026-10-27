module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

@[expose] def NoE32 (G : Type) [Group G] : Prop :=
  ∀ E : Subgroup G, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) → Nat.card ↥E ≤ 16

variable {G : Type} [Group G]

abbrev U4 (z t : G) : Subgroup G := zpowers z ⊔ zpowers t

structure UData (z t : G) : Prop where
  z_sq : z * z = 1
  t_sq : t * t = 1
  comm : z * t = t * z
  z_ne : z ≠ 1
  t_ne : t ≠ 1
  zt_ne : z ≠ t
  conj_zt : IsConj z t
  not_conj : ¬ IsConj z (z * t)

@[expose] def Hstr (z t : G) : Prop :=
  ∀ Q : Subgroup G, Q ≤ centralizer ((U4 z t : Subgroup G) : Set G) → IsPGroup 2 ↥Q → U4 z t ≤ Q →
    Q ≠ U4 z t → ∃ d ∈ Q, orderOf d = 2 ∧ d ∉ U4 z t

structure GoodI1 (H U I₁ : Subgroup G) : Prop where
  le_H : I₁ ≤ H
  comm : ∀ i ∈ I₁, ∀ u ∈ U, u * i = i * u
  layer : barIn H I₁ ≤ layer (HBar H)
  four : ∃ Q : Subgroup G, Q ≤ I₁ ∧ IVK.IsFourSubgroup Q
  noCent : ∀ i ∈ I₁, (∀ j ∈ I₁, ⁅i, j⁆ ∈ pPrimeCoreOf 2 H) → Odd (orderOf i)

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
