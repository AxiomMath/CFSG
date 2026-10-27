module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.FusionCase
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.RankThree.PartOne.KP.SporadicDefs
import CFSG.Sporadic.Schreier.TitsAutD
import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms


@[expose] def KFactTitsThreeCore : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), d.1 = .tits →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ S : Sylow 3 L, GLBCore 3 2 (S : Subgroup L) = ⊤

theorem card_outer_tits_of_mulEquiv {L : Type} [Group L] (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1 = .tits) (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) : Nat.card (Outer L) = 2 := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  obtain ⟨eS⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv L 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  rw [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv eS,
    CFSG.Sporadic.Schreier.Tits.card_outer_titsD]

theorem d2IndexCaseAt_tits_three (hKF : KFactTitsThreeCore) (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1 = .tits) : D2IndexCaseAt (.lie d) fun p => p = 3 := by
  refine d2IndexCaseAt_of_datum fun L _ _ he p hp => ?_
  subst hp
  obtain ⟨e⟩ := he
  refine ⟨?_, Or.inr (Or.inr (Or.inr (hKF L d hd ⟨e⟩)))⟩
  rw [card_outer_tits_of_mulEquiv d hd e]
  norm_num

end CFSG.AGLEmbeddingD2
