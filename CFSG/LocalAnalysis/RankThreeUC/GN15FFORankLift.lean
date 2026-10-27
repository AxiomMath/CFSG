module

public import CFSG.RankThree.PartTwo.Sec16.Item166ResProofDeltaSz
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectSolv

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.RankCore

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

theorem odd_card_center_of_component {Y : Type} [Group Y] [Finite Y] (hO2 : CFSG.pCore 2 Y = ⊥)
    {E : Subgroup Y} (hE : CFSG.Open.IsComponentOf E ⊤) :
    Odd (Nat.card (Subgroup.center ↥E)) := by
  have hLc : CFSG.IsComponent E := (CFSG.isComponent_iff_open E).2 hE
  have hpL : CFSG.pCore 2 ↥E = ⊥ := by
    have h := CFSG.RankThree.PartTwo.Sec16.ProofDeltaSz166.map_pCore_le_pCore_of_isSubnormal
      (p := 2) hLc.2
    rw [hO2] at h
    have h' : (CFSG.pCore 2 ↥E).map E.subtype = ⊥ := le_antisymm h bot_le
    exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥E) E.subtype_injective).1 h'
  exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.odd_card_center_of_pCore_eq_bot hpL

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.RankCore
