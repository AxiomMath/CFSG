module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

structure XData {X : Type} [Group X] [Finite X] (Z : Set X) (M L D O : Subgroup X) (u : X) : Prop where
  D_le : D ≤ L
  O_le : O ≤ D
  mem : u ∈ L
  mem_M : u ∈ M
  sq : u * u = 1
  sup : L = D ⊔ zpowers u
  inf : D ⊓ zpowers u = ⊥
  D_norm : ∀ g ∈ normalizer (L : Set X), ∀ d ∈ D, g * d * g⁻¹ ∈ D
  O_norm : ∀ g ∈ normalizer (L : Set X), ∀ o ∈ O, g * o * g⁻¹ ∈ O
  O_odd : Odd (Nat.card O)
  comm : ∀ d ∈ D, u * d * u⁻¹ * d⁻¹ ∈ O
  O_M : O ≤ M
  bar : ∃ (K : Type) (_ : Group K) (φ : ↥D →* K), Function.Surjective φ ∧
    φ.ker = O.subgroupOf D ∧ CFSG.BenderSuzuki.IsBenderGroup K ∧
    ∃ S : Sylow 2 K, (M.subgroupOf D).map φ = normalizer ((S : Subgroup K) : Set K)
  zset : ∀ z ∈ Z, z ∈ L → (∃ d ∈ D, z = u * d) ∧ ∀ o ∈ O, z ≠ u * o

end CFSG.GH74.Uniqueness
