module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsDef

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

structure HS08AutData (Y : Type*) [Group Y] (S J : Subgroup (MulAut Y)) : Prop where
  card_inner : Nat.card ↥(J ⊓ innerImage Y ⊤) = 16
  card_normalizer : Nat.card ↥(normalizer (J : Set (MulAut Y))) = 3840
  centralizer_le : ∀ α : MulAut Y, (∀ x ∈ J, α * x = x * α) → α ∈ J
  trans_inner : ∀ x ∈ J ⊓ innerImage Y ⊤, x ≠ 1 → ∀ y ∈ J ⊓ innerImage Y ⊤, y ≠ 1 →
    ∃ d ∈ normalizer (J : Set (MulAut Y)), d * x * d⁻¹ = y
  outer_orbits : ∃ R6 R10 : Set (MulAut Y),
    R6 ∪ R10 = {x | x ∈ J ∧ x ∉ innerImage Y ⊤} ∧ Disjoint R6 R10 ∧
      R6.ncard = 6 ∧ R10.ncard = 10 ∧
      (∀ d ∈ normalizer (J : Set (MulAut Y)), ∀ x ∈ R6, d * x * d⁻¹ ∈ R6) ∧
      (∀ d ∈ normalizer (J : Set (MulAut Y)), ∀ x ∈ R10, d * x * d⁻¹ ∈ R10) ∧
      (∀ x ∈ R6, ∀ y ∈ R6, ∃ d ∈ normalizer (J : Set (MulAut Y)), d * x * d⁻¹ = y) ∧
      (∀ x ∈ R10, ∀ y ∈ R10, ∃ d ∈ normalizer (J : Set (MulAut Y)), d * x * d⁻¹ = y)
  outer_involution : ∀ w : MulAut Y, w * w = 1 → w ∉ innerImage Y ⊤ →
    ∃ a : MulAut Y, a * w * a⁻¹ ∈ J
  gen_involutions : closure {x : MulAut Y | x ∈ S ∧ x * x = 1} = S

end CFSG.EvenSporadicStandard.M22Std
