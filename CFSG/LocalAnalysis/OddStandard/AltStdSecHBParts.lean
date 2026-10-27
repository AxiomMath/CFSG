module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecInner
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoMain
public import CFSG.LocalAnalysis.OddStandard.AltStdBalCFinal

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal
open CFSG.ComponentClassification.RestrictedStd.Spor

@[expose] def AltStdBalancedOrder2InnerSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → n ≤ 11 → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → Nat.card S = 2 →
          (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
          (∀ z : G, z ∈ centralizer (L : Set G) → orderOf z = 2 →
            centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) → False

@[expose] def AltStdBalancedOrder2OuterSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → n ≤ 13 → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → Nat.card S = 2 →
          (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
          (∃ z : G, z ∈ centralizer (L : Set G) ∧ orderOf z = 2 ∧
            ¬ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) → False

theorem altStdCyclicBalancedFalse_of_parts
    (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (htri : ExactShapeTrichotomy)
    (hIS : AltStdBalancedOrder2InnerSmall) (hOS : AltStdBalancedOrder2OuterSmall)
    (hII : ShapeTwoCaseIIClassification) : AltStdCyclicBalancedFalse := by
  refine altStdCyclicBalancedFalse_of_inner_outer ?_ ?_
  · intro G _ _ L hS n hn hθ S hcyc h2 hbal hinner
    by_cases hn11 : n ≤ 11
    · exact hIS G L hS n hn hn11 hθ S hcyc h2 hbal hinner
    · exact altStdBalancedOrder2Inner_ge_twelve hlookup hHN hFour G L hS n (by omega) hθ S hcyc
        h2 hbal hinner
  · intro G _ _ L hS n hn hθ S hcyc h2 hbal hex
    by_cases hn13 : n ≤ 13
    · exact hOS G L hS n hn hn13 hθ S hcyc h2 hbal hex
    · exact altStdBalancedOrder2Outer_ge_fourteen htri hII G L hS n (by omega) hθ S hcyc h2 hbal
        hex

end CFSG.OddStandard.AltStdSec
