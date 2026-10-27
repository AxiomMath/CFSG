module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineSixPairFiveDirect

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open

theorem false_of_inner_direct {X : Type} [Group X] [Finite X]
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    {L I E : Subgroup X} (hL : CFSG.IsComponent L) (hI : CFSG.IsComponent I) (hLI : L ≠ I)
    (hdirect : L ⊓ I = ⊥) (h3I : 3 ∣ Nat.card I) (hL2 : 2 ≤ CFSG.Open.pRank 3 L)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 9)
    (hEI : E ≤ Subgroup.normalizer (I : Set X))
    (hfaithI : ∀ e ∈ E, e ≠ 1 → ¬ I ≤ Subgroup.centralizer ({e} : Set X))
    (hinner : ∀ e ∈ E, ∃ k ∈ L, k ^ 3 = 1 ∧ ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹) : False := by
  have hcard : Nat.card E = 3 ^ 2 := by
    rw [hEcard]
    norm_num
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section12.false_of_inner_direct_of_prime
    Nat.prime_three hrank hL hI hLI hdirect h3I hL2 hE hcard hEI hfaithI hinner

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
