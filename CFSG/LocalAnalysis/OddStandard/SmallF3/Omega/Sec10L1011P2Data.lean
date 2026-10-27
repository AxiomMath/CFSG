module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec1011P2Data (L B' : Subgroup G) (c1 c2 : G) : Prop where
  card : Nat.card B' = 2 ^ 4
  comm : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a
  sq : ∀ b ∈ B', b * b = 1
  normL : B' ≤ normalizer (L : Set G)
  c1N : c1 ∈ normalizer (L : Set G)
  c2N : c2 ∈ normalizer (L : Set G)
  c1B : c1 ∈ normalizer (B' : Set G)
  c2B : c2 ∈ normalizer (B' : Set G)
  c1LC : c1 ∈ L ⊔ centralizer (L : Set G)
  c2LC : c2 ∈ L ⊔ centralizer (L : Set G)
  cc : ∀ b ∈ B', c1 * (c2 * b * c2⁻¹) * c1⁻¹ = c2 * (c1 * b * c1⁻¹) * c2⁻¹
  cube1 : ∀ b ∈ B', c1 ^ 3 * b * (c1 ^ 3)⁻¹ = b
  cube2 : ∀ b ∈ B', c2 ^ 3 * b * (c2 ^ 3)⁻¹ = b
  span : ∀ b ∈ B', ∃ b1 ∈ B', ∃ b2 ∈ B',
    b = b1 * (c1 * b1 * c1⁻¹) * (b2 * (c2 * b2 * c2⁻¹))

end CFSG.OddStandard.SmallF3.Omega
