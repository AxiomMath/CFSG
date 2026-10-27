module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Facts

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {G : Type} [Group G]

structure Hyp (G : Type) [Group G] [Finite G] (L A T : Subgroup G) (z t : G) : Prop where
  std : StdHyp G L
  set : TwoCentralSetting G L z t T
  conj_zt : IsConj z (t * z)
  not_conj : ∀ l ∈ L, ¬ IsConj z l
  jc : JcFacts L A T t

@[expose] def B (A : Subgroup G) (z : G) : Subgroup G := A ⊔ zpowers z

@[expose] def M (A : Subgroup G) (z : G) : Subgroup G := normalizer (B A z : Set G)

@[expose] def R₀ (A : Subgroup G) (z : G) : Subgroup G := M A z ⊓ centralizer (A : Set G)

structure E2Facts (L A : Subgroup G) (z : G) : Prop where
  centralizer_B : centralizer (B A z : Set G) = B A z
  M_inf_centralizer : M A z ⊓ centralizer ({z} : Set G) = (L ⊓ normalizer (A : Set G)) ⊔ zpowers z
  M_le : M A z ≤ normalizer (A : Set G)
  conj_mem : ∀ m ∈ M A z, z⁻¹ * (m * z * m⁻¹) ∈ A
  conj_surj : ∀ a ∈ A, ∃ r ∈ R₀ A z, r * z * r⁻¹ = z * a
  card_R₀ : Nat.card (R₀ A z) = 2 ^ 21

structure E3Facts (A : Subgroup G) (z : G) (W : Subgroup G) : Prop where
  A_le : A ≤ W
  le_R₀ : W ≤ R₀ A z
  card : Nat.card W = 2 ^ 20
  z_not_mem : z ∉ W
  M_le : M A z ≤ normalizer (W : Set G)
  mul_self_mem : ∀ w ∈ W, w * w ∈ A
  commutator_mem : ∀ v ∈ W, ∀ w ∈ W, v * w * v⁻¹ * w⁻¹ ∈ A

structure WFacts (L A : Subgroup G) (z : G) (W₁ W₂ : Subgroup G) : Prop where
  elemAb : IsElementaryAbelian 2 ↥(W₁ ⊔ W₂)
  A_le : A ≤ W₁ ⊔ W₂
  le_R₀ : W₁ ⊔ W₂ ≤ R₀ A z
  M_le : M A z ≤ normalizer ((W₁ ⊔ W₂ : Subgroup G) : Set G)
  card₁ : Nat.card W₁ = 2 ^ 10
  card₂ : Nat.card W₂ = 2 ^ 10
  inf_eq_bot : W₁ ⊓ W₂ = ⊥
  inf_A : W₁ ⊓ A = ⊥
  swap : ∀ w ∈ W₁, z * w * z⁻¹ ∈ W₂
  normalizes : ∀ x ∈ L ⊓ normalizer (A : Set G), ∀ w ∈ W₁, x * w * x⁻¹ ∈ W₁

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
