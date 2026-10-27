module

public import CFSG.Open.QTFaithfulEmptyTauCeti
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.Adapters.ExceptionalCatalogReverse

public section

namespace CFSG.Open.QTFaithfulEmptyTauCeti

open CFSG.Assembly

theorem inCatalog_of_catalog
    (X : Type) [Group X] (h : Blueprint.Catalog X) : InCatalog X := by
  rcases h with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hc⟩ | he | ⟨s, ⟨e⟩⟩
  · exact ⟨.cyclic p hp, ⟨e⟩⟩
  · exact ⟨.alternating n hn, ⟨e⟩⟩
  · exact ClassicalModels.inCatalog_of_statedClassicalModel X t n p f hc
  · exact TauCetiBridge.exceptionalRep_inCatalog X he
  · obtain ⟨b⟩ := RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
    exact ⟨.sporadic s, ⟨e.trans b⟩⟩

theorem catalogAgree :
    CatalogAgree := fun X _ _ _ hn =>
  ⟨RankThree.PartOne.TCB.tauCetiCatalogBridge X hn, inCatalog_of_catalog X⟩

end CFSG.Open.QTFaithfulEmptyTauCeti
