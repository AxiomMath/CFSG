module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6XiStep3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapInvLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)

section Transfer

variable {E : Type*} [Group E] [Finite E]

theorem pow_index_center_eq_one_of_commutator_eq_top (hE : commutator E = ⊤) (z : E) :
    z ^ (center E).index = 1 := by
  have hker : commutator E ≤ (MonoidHom.transferCenterPow E).ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (Subgroup.mem_center_iff.1 (MonoidHom.transferCenterPow E g₂).2 _))
  have h1 : MonoidHom.transferCenterPow E z = 1 := hker (hE ▸ Subgroup.mem_top z)
  simpa using congrArg Subtype.val h1

theorem natCard_dvd_natCard_of_surjective_hom {S : Type*} [Group S] {ρ : E →* S}
    (hρ : Function.Surjective ρ) : Nat.card S ∣ Nat.card E := by
  have h : ρ.ker.index = Nat.card S := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hρ, Subgroup.card_top]
  exact h ▸ Subgroup.index_dvd_card _

theorem prime_dvd_card_of_surjective_of_ker_le_center {S : Type*} [Group S]
    (hE : commutator E = ⊤) {ρ : E →* S} (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center E) {p : ℕ} (hp : p.Prime) (hpE : p ∣ Nat.card E) :
    p ∣ Nat.card S := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpE
  have h1 : p ∣ (center E).index := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one (pow_index_center_eq_one_of_commutator_eq_top hE g)
  have h2 : (center E).index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hker
  have h3 : ρ.ker.index = Nat.card S := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hρ, Subgroup.card_top]
  exact h3 ▸ h1.trans h2

end Transfer

theorem thirtyOne_dvd_ordA_five_two : 31 ∣ CFSG.Open.ordA (6 - 1) (2 ^ 1) := by decide

theorem not_thirtyOne_dvd_ordTwistedD_four_two : ¬ 31 ∣ CFSG.Open.ordTwistedD 4 (2 ^ 1) := by
  decide

section Neighbours

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem thirtyOne_dvd_card_centralizerPerfectCore_linear6 {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .linear6) :
    31 ∣ Nat.card (centralizerPerfectCore (subgroupToG e X₀)) := by
  obtain ⟨S, _, hS, ρ, hρ, -, -⟩ :=
    exists_surjective_centralizerPerfectCore_nonsplit_F4_two_graph hw e hXJ hcyc hX₀
      (κ := .linear6) (by decide) hk
  have hcard : Nat.card S = CFSG.Open.ordA (6 - 1) (2 ^ 1) :=
    LinearPilot.card_of_lieModel_PSL_two hS
  exact (hcard ▸ thirtyOne_dvd_ordA_five_two).trans (natCard_dvd_natCard_of_surjective_hom hρ)

theorem not_thirtyOne_dvd_card_centralizerPerfectCore_omegaMinus8 {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .omegaMinus8) :
    ¬ 31 ∣ Nat.card (centralizerPerfectCore (subgroupToG e X₀)) := by
  obtain ⟨S, _, hS, ρ, hρ, hker, -⟩ :=
    exists_surjective_centralizerPerfectCore_nonsplit_F4_two_graph hw e hXJ hcyc hX₀
      (κ := .omegaMinus8) (by decide) hk
  have hcard : Nat.card S = CFSG.Open.ordTwistedD 4 (2 ^ 1) :=
    TwistedE6Pilot.card_of_lieModel_POmegaMinus_four_two hS
  have : Group.IsPerfect (centralizerPerfectCore (subgroupToG e X₀)) :=
    Subgroup.isPerfect_iff.2 (commutator_centralizerPerfectCore _)
  intro h31
  have h := prime_dvd_card_of_surjective_of_ker_le_center Group.IsPerfect.commutator_eq_top hρ
    hker (by norm_num : Nat.Prime 31) h31
  rw [hcard] at h
  exact not_thirtyOne_dvd_ordTwistedD_four_two h

end Neighbours

section Main

theorem twoE6CoreNotDvdInput_holds : TwoE6CoreNotDvdInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' hdvd
  exact not_thirtyOne_dvd_card_centralizerPerfectCore_omegaMinus8 hw (e.trans (graphAutF4 K).symm)
    hXJ hcyc hX₀ hκ' ((thirtyOne_dvd_card_centralizerPerfectCore_linear6 hw e hXJ hcyc hX₀ hκ).trans
      hdvd)

end Main

end CFSG.SeitzReduction.F4Pilot
