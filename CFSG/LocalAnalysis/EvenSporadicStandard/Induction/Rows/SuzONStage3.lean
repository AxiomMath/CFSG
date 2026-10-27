module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONLemma36
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONKFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore CFSG.ONSchreier Cover
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
  CFSG.ComponentClassification.PerfectAutomorphisms

section Suz


theorem hypothesisOne_suz {Y : Type} [Group Y] (h : IsSporadic Y .Suz) : HypothesisOne Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm HypOne.Suz.hypothesisOne_native

theorem twoSylowStd_suz (h25 : Finkelstein77.Asc76Lemma25)
    (hr : ∀ (X : Type) [Group X], IsLS [.Suz] X → 3 ≤ CFSG.pRank 2 X) : TwoSylowStd [.Suz] :=
  twoSylowStd_of_lemma25 h25 hr fun _ _ h => hypothesisOne_suz h

theorem outTwoCovers_suz : OutTwoCovers [.Suz] := by
  intro s hs H _ M hM
  rcases List.mem_singleton.1 hs with rfl
  exact outTwo_of_quotient hM.1.1 (suz_outTwo hM.2.2)

@[expose] def IsKSuz : GroupClass := IsOddCentralExt ↥suzD

theorem isKSuz_inv : GroupClass.IsoInv IsKSuz := IsOddCentralExt.isoInv _

theorem suz_rowIsK : ∀ s ∈ [TauCeti.SporadicName.Suz], ∀ (H : Type) [Group H]
    (L K : Subgroup H) (u : H), OddCover s L → SuzQ H L K u → IsKSuz ↥K := by
  intro s hs H _ L K u hcov hQ
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
  have := hcov.finite (by decide : TauCeti.SporadicName.Suz ≠ .M)
  have hTop := isSporadic_top hcov.2.2
  have hP := suzPair_quotient hcov hu hu2 hKL hKu hKperf hcard
  have F := suz_outFacts hTop hP
  have hpin := pinnedLocal_of_solomonLocal (solomonLocal_suz hTop hP)
    fun c hc => F.normalized c ⟨Subgroup.mem_top c, hc⟩
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL)
    (isQuasisimple_of_quotient (isPerfect_subgroupOf_of_le hKL hKperf) hpin.quasisimple),
    suz_coverMap hcov hu hu2 hKL hKu hKperf hcard⟩

theorem sol78Closing_suz : Sol78Closing [.Suz] (fun _ => SuzQ) :=
  sol78Closing_of_partsP (S := [.Suz]) (Q := fun _ => SuzQ) (P := fun _ => SuzQ)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78SettingLocalQ_suz)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78Local39Q_suz)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact solomonCoreP_suz)

theorem suz_finite_even : ∀ s ∈ [TauCeti.SporadicName.Suz], ∀ (Y : Type) [Group Y],
    IsSporadic Y s → Finite Y ∧ Even (Nat.card Y) := by
  intro s hs Y _ h
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨hfin, -⟩ := suz_simple_data h
  refine ⟨hfin, ?_⟩
  obtain ⟨e⟩ := h
  have hc : Nat.card (Carrier .Suz) = 448345497600 := CFSG.Sporadic.Suz.card_Suz
  rw [Nat.card_congr e.toEquiv, hc]
  decide

def stage3Row_suz (hF : RowAtlasFacts [.Suz] (fun _ => SuzQ) IsKSuz) (haut : SuzAutFix)
    (hperf : SuzInvolutionPerfect) (hfix : SuzFixedNotLam) (h25 : Finkelstein77.Asc76Lemma25) :
    Stage3Row [.Suz] (fun _ => SuzQ) :=
  stage3Row_of_parts (m := fun _ => 2) hF (fun X _ hX => suz_kNotExc X hX)
    (fun _ _ _ _ hX hY => suz_kNeL hX hY) isKSuz_inv (fun X _ hX => hX.1) suz_finite_even
    (fun s hs => by
      rcases List.mem_singleton.1 hs with rfl
      exact Rec36.new 4 (lemma36eDataQ_suz haut hperf hfix))
    outTwoCovers_suz suz_rowIsK (Or.inr (twoSylowStd_suz h25 hF.pRank_L))

end Suz

section ON


theorem on_finite_even : ∀ s ∈ [TauCeti.SporadicName.ONan], ∀ (Y : Type) [Group Y],
    IsSporadic Y s → Finite Y ∧ Even (Nat.card Y) := by
  intro s hs Y _ h
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨hfin, -⟩ := on_simple_data h
  refine ⟨hfin, ?_⟩
  obtain ⟨e⟩ := h
  have e' : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e
  rw [Nat.card_congr e'.toEquiv, CFSG.Sporadic.ON.card_ON]
  decide

theorem outTwoCovers_on : OutTwoCovers [.ONan] := by
  intro s hs H _ M hM
  rcases List.mem_singleton.1 hs with rfl
  exact outTwo_of_quotient hM.1.1 (on_outTwo hM.2.2)

@[expose] def IsKON : GroupClass := IsOddCentralExt ↥onL

theorem isKON_inv : GroupClass.IsoInv IsKON := IsOddCentralExt.isoInv _

theorem on_rowIsK : ∀ s ∈ [TauCeti.SporadicName.ONan], ∀ (H : Type) [Group H]
    (L K : Subgroup H) (u : H), OddCover s L → ONQ H L K u → IsKON ↥K := by
  intro s hs H _ L K u hcov hQ
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
  have := hcov.finite (by decide : TauCeti.SporadicName.ONan ≠ .M)
  have hTop := isSporadic_top hcov.2.2
  have hP := onPair_quotient hcov hu hu2 hKL hKu hKperf hcard
  have F := on_inFacts hTop hP
  have hpin := pinnedLocal_of_solomonLocal (solomonLocal_on hTop hP)
    fun c hc => F.normalized c ⟨Subgroup.mem_top c, hc⟩
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL)
    (isQuasisimple_of_quotient (isPerfect_subgroupOf_of_le hKL hKperf) hpin.quasisimple),
    on_coverMap hcov hu hu2 hKL hKu hKperf hcard⟩

theorem on_u_mem : ∀ s ∈ [TauCeti.SporadicName.ONan], ∀ (H : Type) [Group H]
    (L K : Subgroup H) (u : H), OddCover s L → ONQ H L K u → u ∈ K := by
  intro s hs H _ L K u hcov hQ
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
  have := hcov.finite (by decide : TauCeti.SporadicName.ONan ≠ .M)
  have hTop := isSporadic_top hcov.2.2
  have hP := onPair_quotient hcov hu hu2 hKL hKu hKperf hcard
  exact mem_of_quotient_involution hcov.2.1 hu hu2 (on_inFacts hTop hP).u_mem

theorem sol78Closing_on (hmult : OddMultThree .ONan) (hF : ONOuterFixedPerfect) :
    Sol78Closing [.ONan] (fun _ => ONQ) :=
  sol78Closing_of_partsP (S := [.ONan]) (Q := fun _ => ONQ) (P := fun _ => ONQ)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78SettingLocalQ_on)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78Local39Q_on)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact solomonCoreP_on hmult hF)

def stage3Row_on (hF : RowAtlasFacts [.ONan] (fun _ => ONQ) IsKON) (hfix : ONK2FixedNotLam) :
    Stage3Row [.ONan] (fun _ => ONQ) :=
  stage3Row_of_parts (m := fun _ => 2) hF (fun X _ hX => on_kNotExc X hX)
    (fun _ _ _ _ hX hY => on_kNeL hX hY) isKON_inv (fun X _ hX => hX.1) on_finite_even
    (fun s hs => by
      rcases List.mem_singleton.1 hs with rfl
      exact Rec36.new 2 (lemma36eDataQ_on hfix))
    outTwoCovers_on on_rowIsK (Or.inl on_u_mem)

end ON

end CFSG.EvenSporadicStandard.Induction
