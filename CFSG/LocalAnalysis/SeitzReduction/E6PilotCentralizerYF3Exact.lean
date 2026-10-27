module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3Done
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYLeviUnip

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)


variable {K : Type} [Field K]

theorem factF3y [Finite K] [CharP K 2] :
    perfectCore (centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K))) =
        yRadical K ⊔ yLevi K ∧
      IsPGroup 2 (yRadical K) ∧
      yLevi K ≤ normalizer (yRadical K : Set (adjointGroup .E6 K)) ∧
      Disjoint (yRadical K) (yLevi K) ∧
      (∀ N : Subgroup (yLevi K), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) ≤ yLevi K :=
  factF3y_of_P4 fun _ hu hc =>
    mem_yLeviF4_of_mem_parabolicLeviUnipotent hu (mem_centralizer_singleton_iff.1 hc)

theorem factF3y_lieModel {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    perfectCore (centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K))) =
        yRadical K ⊔ yLevi K ∧
      IsPGroup 2 (yRadical K) ∧
      yLevi K ≤ normalizer (yRadical K : Set (adjointGroup .E6 K)) ∧
      Disjoint (yRadical K) (yLevi K) ∧
      (∀ N : Subgroup (yLevi K), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) ≤ yLevi K ∧
      CFSG.Blueprint.LieModel (yLevi K) .PSp 3 2 f := by
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  exact factF3y_lieModel_of_P4 hK fun _ hu hc =>
    mem_yLeviF4_of_mem_parabolicLeviUnipotent hu (mem_centralizer_singleton_iff.1 hc)

end CFSG.SeitzReduction.E6Pilot
