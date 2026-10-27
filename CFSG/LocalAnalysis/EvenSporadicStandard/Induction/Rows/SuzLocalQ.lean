module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverOut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore Cover

@[expose] def SuzQ (H : Type) [Group H] (L K : Subgroup H) (u : H) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ Group.IsPerfect ↥K ∧
    Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 20160

theorem suzQ_inL : PairClass.InL SuzQ := fun _ _ _ _ _ h => h.1

theorem suzPair_quotient {H : Type} [Group H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .Suz L) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hKperf : Group.IsPerfect ↥K)
    (hcard : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 20160) :
    SuzPair (↥L ⧸ center ↥L) ⊤ ((K.subgroupOf L).map (q ↥L)) (q ↥L ⟨u, hu⟩) := by
  refine ⟨Subgroup.mem_top _, hcov.orderOf_q_involution hu hu2, le_top, ?_, ?_, hcard⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKu k (Subgroup.mem_subgroupOf.1 hk))
  · have := isPerfect_subgroupOf_of_le hKL hKperf
    exact Group.IsPerfect.map _


theorem suz_outFacts {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .Suz) (hQ : SuzPair G L K u) : OutFacts L K u := by
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := suz_model hL hQ
  obtain ⟨M⟩ := suz_outModel
  exact M.outFacts_of_fields hQ.1 hQ.2.1 hQ.2.2.1 (mem_centralizer_iff.2 hQ.2.2.2.1) Ψ hΨ hΨL hΨR
    hΨu hQ.2.2.2.2.1 (hQ.2.2.2.2.2.trans card_suzD.symm)

theorem sol78SettingLocalQ_suz : Sol78SettingLocalQ .Suz SuzQ SuzQ := by
  intro H _ _ L K u hcov hQ
  refine ⟨?_, hQ⟩
  obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
  have hTop := isSporadic_top hcov.2.2
  have hP := suzPair_quotient hcov hu hu2 hKL hKu hKperf hcard
  have F := suz_outFacts hTop hP
  exact solomonLocalQ_of_pinned hcov hu hu2 hKL hKu hKperf
    (pinnedLocal_of_solomonLocal (solomonLocal_suz hTop hP)
      fun c hc => F.normalized c ⟨Subgroup.mem_top c, hc⟩)

theorem sol78Local39Q_suz : Sol78Local39Q .Suz SuzQ := by
  intro H _ _ N L K t u hcov hset hQ
  obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
  have hTop := isSporadic_top hcov.2.2
  have hP := suzPair_quotient hcov hu hu2 hKL hKu hKperf hcard
  exact (outFacts_of_quotient hcov.2.1 hcov.1.1 hu hu2 hKL hKu hKperf
    (suz_outFacts hTop hP)).local39 hu2 hKL (mem_centralizer_iff.2 hKu) hset.hyp35

end CFSG.EvenSporadicStandard.Induction
