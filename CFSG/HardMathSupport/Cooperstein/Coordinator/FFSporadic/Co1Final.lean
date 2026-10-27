module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Native
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CarrierFactsProof
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KernelTrivialThreeCo1
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.DoubleCoversCo1B
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.BigPrimes
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRowsLarge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
open CFSG.RankThree.PerfectCover CFSG.EvenSporadicStandard CFSG.AGLEmbedding

noncomputable def co1CarrierEquiv : NativeSporadic.Co1 ≃* NativeSporadic.Carrier .Co1 :=
  MulEquiv.refl _

theorem co1_card_hopfMultiplier :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .Co1)) = 2 :=
  nativeRow_of_two_one_three_zero rfl (carrierFacts_of_ne_M _ (by decide)) rowBound_Co1
    two_dvd_card_hopfMultiplier_Co1 kernelTrivialAt_three_Co1
    (bigPrimeFacts_of_ne_M .Co1 (by decide))

theorem co1_center_dvd
    (L : Type) [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* NativeSporadic.Co1) :
    Nat.card (Subgroup.center L) ∣ 2 := by
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq (e.trans co1CarrierEquiv)
  rwa [co1_card_hopfMultiplier] at h

theorem co1_autInner :
    ∀ φ : NativeSporadic.Co1 ≃* NativeSporadic.Co1, ∃ s : NativeSporadic.Co1,
      ∀ x, φ x = s * x * s⁻¹ := by
  intro φ
  obtain ⟨g, hg⟩ := Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
      Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner φ
  exact ⟨g, fun x => by rw [hg, MulAut.conj_apply]⟩

theorem noIrrFFOffender_Co1_native :
    NoIrrFFOffender NativeSporadic.Co1 := by
  obtain ⟨D⟩ := cutData_Co1
  exact noIrrFFOffender_of_cutData D co1_autInner fun L _ _ hq ⟨e⟩ => co1_center_dvd L hq e

theorem noIrrFFOffender_Co1 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .Co1).Group :=
  noIrrFFOffender_transfer noIrrFFOffender_Co1_native CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_Co1 :
    GF2NoFFSporadicFor .Co1 :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_Co1

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
