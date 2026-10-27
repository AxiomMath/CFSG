module

public import CFSG.HardMathSupport.Foote.Proving.ModelFinite
public import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultSporadicFi
public import CFSG.Sporadic.Catalog.Finiteness
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.U62Odd

open Subgroup CFSG.Blueprint.Multiplier CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Induction

theorem odd_card_center_of_lieModel_psl_six_four
    {L : Type} [Group L] (hq : CFSG.IsQuasisimple L)
    (hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .PSL 6 2 2) :
    Odd (Nat.card (center L)) := by
  have hmodel' := hmodel.statedClassicalModel (by decide)
  haveI : Finite (L ⧸ center L) :=
    CFSG.HardMathSupport.Foote.Proving.finite_of_statedClassicalModel _ _ _ _ _ hmodel'
  haveI : Finite L :=
    CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hq
      (MulEquiv.refl _)
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hq.1
    (MulEquiv.refl (L ⧸ center L))
  obtain ⟨e⟩ := (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hmodel').2
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 6 2 2 = (3, 1) := by decide
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 6 2 2 = (1, 1) := rfl
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (L ⧸ center L)) = 3 := by
    rw [Nat.card_congr e.toEquiv]
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    rw [hgen, hexc]
    simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]
  rw [hcard] at hdvd
  exact Odd.of_dvd_nat (by decide : Odd 3) hdvd

theorem center_eq_bot_of_fi23_of_sporadicMultipliers
    (hSM : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (hX : IsSporadic (X ⧸ center X) .Fi23) : center X = ⊥ := by
  haveI : Finite (Carrier .Fi23) :=
    CFSG.Sporadic.Catalog.finite_carrier_of_ne_M .Fi23 (by decide)
  have hX' : IsSporadic (X ⧸ center X) .Fi23 := hX
  obtain ⟨e⟩ := hX
  haveI : Finite (X ⧸ center X) := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite X :=
    CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hq e
  exact fi23Mult_of_sporadicMultipliers hSM X hq hX'

theorem odd_card_center_of_fi24_of_sporadicMultipliers
    (hSM : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (hX : IsSporadic (X ⧸ center X) .Fi24Prime) : Odd (Nat.card (center X)) := by
  haveI : Finite (Carrier .Fi24Prime) :=
    CFSG.Sporadic.Catalog.finite_carrier_of_ne_M .Fi24Prime (by decide)
  have hX' : IsSporadic (X ⧸ center X) .Fi24Prime := hX
  obtain ⟨e⟩ := hX
  haveI : Finite (X ⧸ center X) := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite X :=
    CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hq e
  exact fi24Mult_of_sporadicMultipliers hSM X hq hX'

theorem not_hasEvenCover_of_overgroup_of_sporadicMultipliers
    (hSM : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    {N : Type} [Group N]
    (h : CFSG.Blueprint.LieModel N .PSL 6 2 2 ∨ IsSporadic N .Fi23 ∨
      IsSporadic N .Fi24Prime) :
    ¬ CFSG.EvenSporadicStandard.Induction.Fi.Eng.HasEvenCover N := by
  rintro ⟨Q₀, _, hq, heven, ⟨e⟩⟩
  rcases h with hL | h23 | h24
  · have hL' : CFSG.Blueprint.LieModel (Q₀ ⧸ center Q₀) .PSL 6 2 2 :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL
    exact (Nat.not_even_iff_odd.mpr (odd_card_center_of_lieModel_psl_six_four hq hL')) heven
  · have h23' : IsSporadic (Q₀ ⧸ center Q₀) .Fi23 := by
      obtain ⟨f⟩ := h23
      exact ⟨e.trans f⟩
    rw [center_eq_bot_of_fi23_of_sporadicMultipliers hSM hq h23', Subgroup.card_bot] at heven
    exact (Nat.not_even_iff_odd.mpr odd_one) heven
  · have h24' : IsSporadic (Q₀ ⧸ center Q₀) .Fi24Prime := by
      obtain ⟨f⟩ := h24
      exact ⟨e.trans f⟩
    exact (Nat.not_even_iff_odd.mpr (odd_card_center_of_fi24_of_sporadicMultipliers hSM hq h24')) heven

section Unconditional

theorem not_hasEvenCover_of_overgroup
    {N : Type} [Group N]
    (h : CFSG.Blueprint.LieModel N .PSL 6 2 2 ∨ IsSporadic N .Fi23 ∨
      IsSporadic N .Fi24Prime) :
    ¬ CFSG.EvenSporadicStandard.Induction.Fi.Eng.HasEvenCover N :=
  not_hasEvenCover_of_overgroup_of_sporadicMultipliers
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds h

end Unconditional

end CFSG.EvenSporadicStandard.Induction.Fi.U62Odd
