module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MOddCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HLambda

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.TwoHS

@[expose] def HNFixesElem : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover .HN L →
    HNPair H L K u → InvolutionFixesElem ↥K 16

@[expose] def HNOddCore : Prop := AutOddCoreTrivial NativeSporadic.HN

theorem sol78Local39Q_hn (hmult : OddMultTrivial .HN) : Sol78Local39Q .HN HNPair := by
  intro H _ _ N L K t u hcov hset hP
  have hL : IsSporadic L .HN := hcov.isSporadic_of_mult hmult
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hP
  obtain ⟨hcovS, hidx⟩ := hn_pair_cover hL huL hu2 hKL hKu hcard
  have hlt : 11 < (Nat.card L).factorization 2 := by
    rw [hn_card_eq hL, hn_factorization_two]
    norm_num
  exact sol78Local39Q_of_hsCover hset huL hcovS hidx hlt
    (hn_overgroups_of_fact hnOvergroupFact hL huL hu2 hKL hKu hcard)

theorem solomonLocalQ_hn (hmult : OddMultTrivial .HN) {H : Type} [Group H] [Finite H]
    {L K : Subgroup H} {u : H} (hcov : OddCover .HN L) (hQ : HNPair H L K u) :
    SolomonLocalQ L K u := by
  have hL : IsSporadic L .HN := hcov.isSporadic_of_mult hmult
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  obtain ⟨hcovS, -⟩ := hn_pair_cover hL huL hu2 hKL hKu hcard
  exact solomonLocalQ_of_hsCover hcov (hn_outTwo_of_isSporadic hL) huL hu2 hKL hKu hcovS

theorem sol78SettingLocalQ_hn (hmult : OddMultTrivial .HN) :
    Sol78SettingLocalQ .HN HNPair HNPair := by
  intro H _ _ L K u hcov hQ
  exact ⟨solomonLocalQ_hn hmult hcov hQ, hQ⟩

theorem lemma36DataQ_hn (hmult : OddMultTrivial .HN) (hfix : HNFixesElem) :
    Lemma36DataQ .HN HNPair 2 16 := by
  refine ⟨by norm_num, ?_⟩
  intro H _ _ L K u hcov hQ
  have hL : IsSporadic L .HN := hcov.isSporadic_of_mult hmult
  have hQ' := hQ
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  obtain ⟨hcovS, hidx⟩ := hn_pair_cover hL huL hu2 hKL hKu hcard
  have hKC : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  obtain ⟨huK, hC⟩ := central_eq_of_hsCover huL hu2 hcovS
  have hcentC := card_centralizer_le_two_of_central_eq huL hu2 hKL hC
  have hout : OutTwo ↥L := hn_outTwo_of_isSporadic hL
  refine ⟨hu2, huK, hKC, ?_,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC)
      (isComponent_of_isHSCover hcovS).1,
    isSolvable_autCentralizer_of_card_le (card_autCentralizer_le hout hcentC),
    twoAdic_autCentralizer_le hout hcentC, hfix H L K u hcov hQ'⟩
  rw [eq_commutator_of_perfect_of_index_two hcovS.normal hcovS.perfect.commutator_eq_top hidx]
  infer_instance

theorem fusionRowData_hn (hodd : HNOddCore) : FusionRowData .HN (fun _ _ _ => False) :=
  ⟨fun _ _ h => (hn_autCenterCond centerInvolutions_jh h).toExc, fun _ _ h => hn_umovesCond h,
    fun Y _ h => by
      obtain ⟨e⟩ := h
      have e' : Y ≃* NativeSporadic.HN := e
      exact @AutOddCoreTrivial.of_mulEquiv Y NativeSporadic.HN _ inferInstance e' hodd⟩

theorem hnPair_inL : PairClass.InL HNPair := fun _ _ _ _ _ h => h.1

theorem excExcluded_hn : ExcExcluded .HN (fun _ _ _ => False) HNPair := by
  intro H _ _ N L K t u hcov hset hQ u₁ hN _ _ _ h
  exact h

theorem solomonCoreP_hn (hodd : HNOddCore) : SolomonCoreP .HN HNPair :=
  solomonCoreP_of_fusion .HN (fun _ _ _ => False) HNPair hnPair_inL (fusionRowData_hn hodd)
    excExcluded_hn

theorem sol78Closing_hn (hmult : OddMultTrivial .HN) (hodd : HNOddCore) :
    Sol78Closing [.HN] (fun _ => HNPair) :=
  sol78Closing_of_partsP (S := [.HN]) (Q := fun _ => HNPair) (P := fun _ => HNPair)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78SettingLocalQ_hn hmult)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78Local39Q_hn hmult)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact solomonCoreP_hn hodd)

end CFSG.EvenSporadicStandard.Induction
