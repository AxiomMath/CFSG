module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYStabBruhat
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3Final
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYLeviWeyl

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)


variable {K : Type} [Field K]

theorem leviStabilizerAS_of_P4 [CharP K 2]
    (hP4 : ∀ u ∈ parabolicLeviUnipotent .E6 K nodes16,
      u ∈ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) → u ∈ yLeviF4 K) :
    LeviStabilizerAS K :=
  leviStabilizerAS_of_unipotent hP4 fun _ hw hab => canonicalRep_mem_yLeviF4 hw hab

theorem factF3y_of_P4 [Finite K] [CharP K 2]
    (hP4 : ∀ u ∈ parabolicLeviUnipotent .E6 K nodes16,
      u ∈ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) → u ∈ yLeviF4 K) :
    perfectCore (centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K))) =
        yRadical K ⊔ yLevi K ∧
      IsPGroup 2 (yRadical K) ∧
      yLevi K ≤ normalizer (yRadical K : Set (adjointGroup .E6 K)) ∧
      Disjoint (yRadical K) (yLevi K) ∧
      (∀ N : Subgroup (yLevi K), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) ≤ yLevi K :=
  factF3y_of_leviStabilizerAS (leviStabilizerAS_of_P4 hP4)


theorem factF3y_lieModel_of_P4 {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hP4 : ∀ u ∈ parabolicLeviUnipotent .E6 K nodes16,
      u ∈ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) → u ∈ yLeviF4 K) :
    perfectCore (centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K))) =
        yRadical K ⊔ yLevi K ∧
      IsPGroup 2 (yRadical K) ∧
      yLevi K ≤ normalizer (yRadical K : Set (adjointGroup .E6 K)) ∧
      Disjoint (yRadical K) (yLevi K) ∧
      (∀ N : Subgroup (yLevi K), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) ≤ yLevi K ∧
      CFSG.Blueprint.LieModel (yLevi K) .PSp 3 2 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := factF3y_of_P4 (K := K) hP4
  exact ⟨h1, h2, h3, h4, h5, h6, lieModel_yLevi hK⟩

end CFSG.SeitzReduction.E6Pilot
