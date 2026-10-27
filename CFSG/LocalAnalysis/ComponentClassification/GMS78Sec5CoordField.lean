module

import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsField
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ComponentClassification.GMS78.VLike

section Equivariant

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] [Fintype K]

omit [Fintype K] in
theorem linear_of_equivariant {f : K → K} {μ : K} (hf : ∀ w, f (μ * w) = μ * f w)
    (h0 : f 0 = 0) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) (w : K) : f w = f 1 * w := by
  apply CFSG.SeitzReduction.RankOne.SzCoords.linear_of_equivariant <;> assumption

theorem bilinear_of_equivariant' [CharP K 2] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (β : K → K → K)
    (h1 : ∀ u u' w, β (u + u') w = β u w + β u' w) (h2 : ∀ u w w', β u (w + w') = β u w + β u w')
    {κ : K} (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hβ : ∀ u w, β (κ * u) (κ ^ (2 ^ (a + 1) + 1) * w) = κ ^ (2 ^ (a + 1) + 1) * β u w) :
    ∃ c : K, ∀ u w, β u w = c * (u * w) ^ 2 ^ a := by
  apply CFSG.SeitzReduction.RankOne.SzCoords.bilinear_of_equivariant' <;> assumption

end Equivariant

end CFSG.ComponentClassification.GMS78.VLike
