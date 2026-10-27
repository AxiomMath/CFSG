module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6XiCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6CaseNotDvd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)

theorem not_eleven_dvd_ordD_four_two : ¬ 11 ∣ CFSG.Open.ordD 4 (2 ^ 1) := by
  decide

section Neighbour


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem not_eleven_dvd_card_centralizerPerfectCore_omegaPlus8 {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .omegaPlus8) :
    ¬ 11 ∣ Nat.card (centralizerPerfectCore (subgroupToG e X₀)) := by
  obtain ⟨S, _, hS, ρ, hρ, hker, -⟩ :=
    exists_surjective_centralizerPerfectCore_nonsplit_F4_two_graph hw e hXJ hcyc hX₀
      (κ := .omegaPlus8) (by decide) hk
  have hcard : Nat.card S = CFSG.Open.ordD 4 (2 ^ 1) :=
    OmegaPilot.card_of_lieModel_POmega_two (Or.inl rfl) hS
  have : Group.IsPerfect (centralizerPerfectCore (subgroupToG e X₀)) :=
    Subgroup.isPerfect_iff.2 (commutator_centralizerPerfectCore _)
  intro h11
  have h := prime_dvd_card_of_surjective_of_ker_le_center Group.IsPerfect.commutator_eq_top hρ
    hker (by norm_num : Nat.Prime 11) h11
  rw [hcard] at h
  exact not_eleven_dvd_ordD_four_two h

end Neighbour

section Main


theorem twoOmegaPlusEightCoreElevenInput_holds : TwoOmegaPlusEightCoreElevenInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ
  exact not_eleven_dvd_card_centralizerPerfectCore_omegaPlus8 hw e hXJ hcyc hX₀ hκ

theorem twoTwistedE6CoreNotDvdInput_holds : TwoTwistedE6CoreNotDvdInput :=
  twoTwistedE6CoreNotDvdInput_of_omegaPlus8 twoOmegaPlusEightCoreElevenInput_holds

theorem twoTwistedE6SpanConjugateInput_holds : TwoTwistedE6SpanConjugateInput :=
  twoTwistedE6SpanConjugateInput_of_notDvd twoTwistedE6CoreNotDvdInput_holds

end Main

end CFSG.SeitzReduction.F4Pilot
