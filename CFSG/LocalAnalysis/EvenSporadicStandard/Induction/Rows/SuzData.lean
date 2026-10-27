module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OddCoreFree
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SuzFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.AutModelTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78


theorem suz_simple_data {Y : Type} [Group Y] (h : IsSporadic Y .Suz) :
    Finite Y ∧ IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card (Carrier .Suz) = 448345497600 := CFSG.Sporadic.Suz.card_Suz
  have : Finite (Carrier .Suz) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hY : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  exact ⟨hY, suz_isSimpleGroup_of_isSporadic ⟨e⟩, suz_exists_not_commute ⟨e⟩⟩

theorem suz_outTwo {Y : Type} [Group Y] (h : IsSporadic Y .Suz) : OutTwo Y := by
  obtain ⟨e⟩ := h
  exact OutTwo.of_mulEquiv (e.trans CFSG.Sporadic.SuzOddCore.suzEquivM).symm
    suz_autRowData.outTwo

theorem suz_autOddCoreTrivial {Y : Type} [Group Y] (h : IsSporadic Y .Suz) :
    AutOddCoreTrivial Y := by
  obtain ⟨hfin, hs, hna⟩ := suz_simple_data h
  obtain ⟨e⟩ := h
  exact autOddCoreTrivial_of_sporadicOddCoreFree
    CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Suz hna e

theorem suz_fusionRowData : FusionRowData .Suz (fun _ _ _ => False) where
  autCenter _ _ h := (suz_autCenterCond_of_isSporadic h).toExc
  uMoves _ _ h := suz_umovesCond_of_isSporadic h
  oddCore _ _ h := suz_autOddCoreTrivial h

end CFSG.EvenSporadicStandard.Induction
