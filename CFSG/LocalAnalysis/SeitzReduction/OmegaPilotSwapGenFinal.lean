module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsLagrangian

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

theorem false_of_swapRow_omega_minus_complete (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_five_le hn) b c))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {m f' : ℕ}
    (hHR8 : ∀ k : Fin (n - 1), ∀ htX : t ∈ centralizer
        (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) : Set G)))
            ⟨t, htX⟩)
        (((modelToG e (minusPairPerp (K := K) (one_le_of_five_le hn) b c k)).subgroupOf
            (centralizer (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) :
              Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k) :
              Set G))))) m f')
    (hrow : ∀ k : Fin (n - 1),
      OmegaRowAt t (modelToG e (minusPairTorus (K := K) (one_le_of_five_le hn) b c k))
        (modelToG e (minusPairPerp (K := K) (one_le_of_five_le hn) b c k)) .swap) : False := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact false_of_swapRow_omega_minus_final hset hKc hq hn hirr e ht hKt hHR8 hrow
    (minusSwapOverlapInput_of_five_le hq hn _ hirr)

end CFSG.SeitzReduction.OmegaPilot
