module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Idx2Q
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MOddCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HLambda

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def BFixesElem : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover .B L →
    BPair H L K u → InvolutionFixesElem ↥K 8

@[expose] def BabyOddCore : Prop := InvolutionOddCoreTrivial NativeSporadic.B

theorem twoAdic_lt_of_idx2Cover_b {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic L .B) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcard : Nat.card K = 2 * ordTwistedE6 2)
    (hcov : IsIdx2Cover ↥(L ⊓ centralizer ({u} : Set H))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set H)))) :
    twoAdic (L ⊓ centralizer ({u} : Set H)) < twoAdic L := by
  have hKC : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hCu : Nat.card ↥(L ⊓ centralizer ({u} : Set H)) = 2 * Nat.card K := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf (L ⊓ centralizer ({u} : Set H)))
    rw [hcov.index_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv] at h1
    omega
  unfold twoAdic
  rw [hCu, hcard, b_card_of_isSporadic hL, factorization_two_cent_b,
    factorization_two_monsterBabyOrder]
  norm_num

theorem sol78Local39Q_b (hf : BabyCoverFacts) (hmult : OddMultTrivial .B) :
    Sol78Local39Q .B BPair := by
  intro H _ _ N L K t u hcov hset hP
  have hL : IsSporadic L .B := hcov.isSporadic_of_mult hmult
  have hpair : BPair H L K u := hP
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hP
  have hcovI := hf.cover H L K u hL hpair
  exact sol78Local39Q_of_idx2Cover hset huL hcovI
    (twoAdic_lt_of_idx2Cover_b hL hKL hKu hcard hcovI) (hf.sylow H L K u hL hpair)
    (hf.aut H L K u hL hpair) (hf.overgroups H L K u hL hpair)

theorem solomonLocalQ_b (hf : BabyCoverFacts) (hmult : OddMultTrivial .B) {H : Type} [Group H]
    [Finite H] {L K : Subgroup H} {u : H} (hcov : OddCover .B L) (hQ : BPair H L K u) :
    SolomonLocalQ L K u := by
  have hL : IsSporadic L .B := hcov.isSporadic_of_mult hmult
  obtain ⟨e⟩ := hL
  have hLB : IsSporadic L .B := ⟨e⟩
  exact solomonLocalQ_of_idx2Cover hcov (outTwo_of_allInner (b_data_of_simple e).1) hQ.1 hQ.2.1
    hQ.2.2.1 hQ.2.2.2.1 (hf.cover H L K u hLB hQ)

theorem sol78SettingLocalQ_b (hf : BabyCoverFacts) (hmult : OddMultTrivial .B) :
    Sol78SettingLocalQ .B BPair BPair := by
  intro H _ _ L K u hcov hQ
  exact ⟨solomonLocalQ_b hf hmult hcov hQ, hQ⟩

theorem lemma36DataQ_b (hf : BabyCoverFacts) (hmult : OddMultTrivial .B) (hfix : BFixesElem) :
    Lemma36DataQ .B BPair 1 8 := by
  refine ⟨by norm_num, ?_⟩
  intro H _ _ L K u hcov hQ
  have hL : IsSporadic L .B := hcov.isSporadic_of_mult hmult
  obtain ⟨e⟩ := hL
  have hLB : IsSporadic L .B := ⟨e⟩
  have hQ' := hQ
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  have hcovI := hf.cover H L K u hLB hQ'
  have hKC : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hcentC := card_centralizer_le_two_of_idx2Cover huL hu2 hKL hcovI
  have hout : OutTwo ↥L := outTwo_of_allInner (b_data_of_simple e).1
  have hqE : CFSG.IsQuasisimple ↥(K.subgroupOf (L ⊓ centralizer ({u} : Set H))) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 hcovI.quasisimple
  refine ⟨hu2, (central_eq_of_idx2Cover huL hu2 hcovI).1, hKC, ?_,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC) hqE,
    isSolvable_autCentralizer_of_card_le (card_autCentralizer_le hout hcentC),
    twoAdic_autCentralizer_le_one_of_allInner (b_data_of_simple e).1 hcentC,
    hfix H L K u hcov hQ'⟩
  rw [hcovI.eq_commutator]
  infer_instance

theorem fusionRowData_b (hodd : BabyOddCore) : FusionRowData .B (fun _ _ _ => False) := by
  have key : ∀ (Y : Type) [Group Y], IsSporadic Y .B →
      AutCenterCond Y ∧ UMovesCond Y ∧ AutOddCoreTrivial Y := by
    intro Y _ h
    have hs := b_isSimpleGroup_of_isSporadic h
    have hnab := b_exists_not_commute h
    obtain ⟨e⟩ := h
    obtain ⟨hinn, hcen, hcomm⟩ := b_data_of_simple e
    have hZ : center Y = ⊥ := center_eq_bot_of_simple_nonabelian hnab
    have e' : Y ≃* NativeSporadic.B := e
    exact ⟨autCenterCond_of_inner hinn hZ hcen, umovesCond_of_inner hinn hZ hcomm,
      autOddCoreTrivial_of_allInner hinn hZ
        (@InvolutionOddCoreTrivial.of_mulEquiv Y NativeSporadic.B _ inferInstance e' hodd)⟩
  exact ⟨fun Y _ h => (key Y h).1.toExc, fun Y _ h => (key Y h).2.1,
    fun Y _ h => (key Y h).2.2⟩

theorem bPair_inL : PairClass.InL BPair := fun _ _ _ _ _ h => h.1

theorem excExcluded_b : ExcExcluded .B (fun _ _ _ => False) BPair := by
  intro H _ _ N L K t u hcov hset hQ u₁ hN _ _ _ h
  exact h

theorem solomonCoreP_b (hodd : BabyOddCore) : SolomonCoreP .B BPair :=
  solomonCoreP_of_fusion .B (fun _ _ _ => False) BPair bPair_inL (fusionRowData_b hodd)
    excExcluded_b

theorem sol78Closing_b (hf : BabyCoverFacts) (hmult : OddMultTrivial .B) (hodd : BabyOddCore) :
    Sol78Closing [.B] (fun _ => BPair) :=
  sol78Closing_of_partsP (S := [.B]) (Q := fun _ => BPair) (P := fun _ => BPair)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78SettingLocalQ_b hf hmult)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78Local39Q_b hf hmult)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact solomonCoreP_b hodd)

end CFSG.EvenSporadicStandard.Induction
