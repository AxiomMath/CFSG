module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.NoIrrEngines
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KernelTrivialThreeFi23
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.BigPrimes
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFischer
public import Certificates.Certificate129030
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Ledger
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.SporadicPerfect

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Blueprint CFSG.F3.Native CFSG.Sporadic.Fi23
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
open CFSG.RankThree.PerfectCover CFSG.EvenSporadicStandard

theorem fi23_heisCfg :
    ∃ (x y : Fin 4 → NativeSporadic.Fi23) (z : NativeSporadic.Fi23),
      HeisCfg 3 4 x y z ∧ ∀ i, y i ^ 3 = 1 :=
  Certificates.certificate129030

theorem fi23_outer_bound
    (B : Subgroup (MulAut NativeSporadic.Fi23)) (_ : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (_ : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 1 * Nat.card ↥(B ⊓ (MulAut.conj : NativeSporadic.Fi23 →* MulAut _).range) := by
  have hle : B ≤ (MulAut.conj : NativeSporadic.Fi23 →* MulAut _).range := by
    intro φ _
    obtain ⟨g, rfl⟩ := CFSG.Sporadic.FischerOddCore.fi23_mulAut_eq_conj φ
    exact ⟨g, rfl⟩
  rw [inf_eq_left.2 hle, one_mul]

noncomputable def fi23CarrierEquiv : NativeSporadic.Fi23 ≃* NativeSporadic.Carrier .Fi23 :=
  MulEquiv.refl _

theorem fi23_carrierFacts : CarrierFacts .Fi23 := by
  have hs : IsSimpleGroup NativeSporadic.Fi23 := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  have hcard : Nat.card NativeSporadic.Fi23 = 4089470473293004800 :=
    CFSG.Sporadic.Fi23.card_Fi23
  have hfin : Finite NativeSporadic.Fi23 :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hperf : Group.IsPerfect NativeSporadic.Fi23 :=
    isPerfect_of_isSimpleGroup_of_not_prime hs
      (Proving.not_prime_card_of_even_gt_two hcard (by norm_num) (by norm_num))
  exact ⟨hfin, hs, hperf, @exists_not_commute_of_perfect_simple _ _ hperf hs⟩

theorem fi23_card_hopfMultiplier
    : Nat.card (hopfMultiplier (NativeSporadic.Carrier .Fi23)) = 1 :=
  nativeRow_of_two_zero_three_zero (s := .Fi23) rfl fi23_carrierFacts rowBound_Fi23
    kernelTrivialAt_three_Fi23 (Proving.bigPrimeFacts_of_ne_M .Fi23 (by decide))

theorem fi23_center_card
    (L : Type) [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* NativeSporadic.Fi23) : Nat.card (Subgroup.center L) = 1 := by
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq (e.trans fi23CarrierEquiv)
  rw [fi23_card_hopfMultiplier] at h
  exact Nat.dvd_one.1 h

theorem noIrrFFOffender_Fi23_native
    : NoIrrFFOffender NativeSporadic.Fi23 := by
  have h1 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have h2 : (2 : ZMod 3) ≠ 1 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨_, _, _, h, hy⟩ := fi23_heisCfg
  have hord : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime h1 h2
  refine noIrrFFOffender_of_heisCfg (k := 1) (c := 1) (p := 3) (n := 4) (by norm_num)
    fi23_outer_bound ?_ h hy ?_
  · intro L _ _ hq he _
    obtain ⟨e⟩ := he
    have hc := fi23_center_card L hq e
    exact ⟨by rw [hc]; norm_num, hc.le⟩
  · rw [hord, CFSG.Sporadic.Fi23.card_Fi23]
    norm_num

theorem noIrrFFOffender_Fi23
    : NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .Fi23).Group :=
  noIrrFFOffender_transfer noIrrFFOffender_Fi23_native
    CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_Fi23
    : GF2NoFFSporadicFor .Fi23 :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_Fi23

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
