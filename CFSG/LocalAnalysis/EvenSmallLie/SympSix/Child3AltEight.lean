module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3AltEightLayer
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3AltEightSectors
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Selector
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOmega
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU33
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3Spor

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup

@[expose] def AltEightSelectorStmt : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (D : Subgroup Y) (a : Y) (J : Subgroup Y),
    GL3Source D a J → CFSG.IsStandardSubgroup J → CFSG.Blueprint.Catalog D →
    Nat.card D ∣ Nat.card (GL (Fin 9) (ZMod 2)) → Sector D

section Selector


theorem gapAltEight_of_selector
    (hD : CFSG.LocalAnalysis.SteinbergBV.DirectSimpleInvolutionCentralizerLayerStmt)
    (hsel : AltEightSelectorStmt) : GapAltEight := by
  intro G _ _ L T z hS V _ _ _ b hb hnd hV φ e he halt hsimple
  have h := alt8_layer_facts φ he z hD hS hb hnd hV halt hsimple
  have hsrc := h.source hsimple
  obtain ⟨n, f, hn, hf, k, _, hk, ⟨η⟩⟩ := sector_evenLinear_of_GL3Source hsrc h.JLBar_standard
    (hsel _ _ _ _ hsrc h.JLBar_standard h.catalog h.card_dvd)
  exact h.false_of_evenLinear hb hnd hV hsimple hn hf hk η

end Selector

section Schreier


theorem gapAltEight_of_selector' (hsel : AltEightSelectorStmt) : GapAltEight :=
  gapAltEight_of_selector
    (CFSG.LocalAnalysis.SteinbergBV.direct_simple_involution_centralizer_layer_of_schreier
      CFSG.RankThree.PartOne.SPOR.schreierFor_catalog) hsel

end Schreier

section Nine


theorem altEightSelector_of (hres : ResidualExclusionsNine) : AltEightSelectorStmt :=
  fun _ _ _ _ _ _ h _ hcat hord => layer_sector_of_GL3_source_nine hres h hcat hord

end Nine

section Final


theorem gapAltEight : GapAltEight :=
  gapAltEight_of_selector' (altEightSelector_of
    ⟨orthogonalExclusions.plus4, orthogonalExclusions.minus4, orthogonalExclusions.plus5,
      excluded_psu33, SelK3.excluded_J2, SelK3.excluded_He⟩)

end Final

end CFSG.EvenSmallLie.Child3
