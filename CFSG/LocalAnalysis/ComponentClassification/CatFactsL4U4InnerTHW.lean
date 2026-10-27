module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerTL4HW
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerTU4HW

public section

namespace CFSG.ComponentClassification.CatFactsL4U4HW

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

theorem cfRow516InnerTHW : CFRow516InnerTHW := by
  intro H _ _ h hrow hin
  obtain ⟨hZ, p, f, hp, hp2, -, hJ, hL | hU⟩ := inner_structure h hrow hin
  · obtain ⟨hq, F, _, _, hF, ⟨e⟩⟩ := hL
    exact innerT_L4 h hrow hin hp hp2 hJ hZ hq hF e
  · obtain ⟨hq, K', _, hUF, ⟨e⟩⟩ := hU
    exact innerT_U4 h hrow hin hp hp2 hJ hZ hq hUF e

end CFSG.ComponentClassification.CatFactsL4U4HW
