module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SevenSwapRow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2HR8Inputs

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def LinearTwoFiveSixInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 5 ≤ n → n ≤ 6 →
    ∀ (_ : L ≃* LinearFlag.projectiveSL n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False


theorem false_of_linear_two_of_seven_le_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : SeitzSetting G L) {n : ℕ}
    (hSpor : CatSLmSporadicAt (n - 2)) {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 7 ≤ n) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : False :=
  false_of_linear_two_of_seven_le hset
    (slmCatalogueClausesAt_of_gls3_sporadic (by omega) hGLS hSpor) (slmEvenTypeDetAt (by omega))
    hK e hn ht hKt

theorem linearTwoInput_of_fiveSix (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : ∀ m, 5 ≤ m → CatSLmSporadicAt m) (h56 : LinearTwoFiveSixInput) : LinearTwoInput := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt
  by_cases h6 : n ≤ 6
  · exact h56 G L hset n K hK hn h6 e t ht hKt
  · exact false_of_linear_two_of_seven_le_of_inputs hGLS hset (hSpor (n - 2) (by omega)) hK e
      (by omega) ht hKt

end CFSG.SeitzReduction.LinearPilot
