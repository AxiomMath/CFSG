module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Open

variable {G : Type} [Group G]

@[expose] def OutU33 : Prop :=
  ∀ (X : Type) [Group X], IsUThreeThree X → AutThreePowInner X

@[expose] def OutL5 : Prop :=
  ∀ (X : Type) [Group X], IsL5Two X → AutThreePowInner X

theorem clauseO_tightRow [Finite G] (hU : OutU33) (hL5 : OutL5) {M S L : Subgroup G}
    (hL : IsWeakSBlock M S L)
    (h : TightRow M L ∨ IsL5Two (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) :
    ClauseO M L := by
  rcases h with (he | ⟨-, he⟩ | he | hu) | h5
  · obtain ⟨e⟩ := he
    exact clauseO_of_cover hL.le hL.perfect (autThreePowInner_alt_of_five_le (N := 6) (by omega)) e
  · obtain ⟨e⟩ := he
    exact clauseO_of_cover hL.le hL.perfect (autThreePowInner_alt_of_five_le (N := 7) (by omega)) e
  · obtain ⟨e⟩ := he
    exact clauseO_of_cover hL.le hL.perfect (autThreePowInner_alt_of_five_le (N := 8) (by omega)) e
  · exact clauseO_of_cover hL.le hL.perfect (hU _ hu) (MulEquiv.refl _)
  · exact clauseO_of_cover hL.le hL.perfect (hL5 _ h5) (MulEquiv.refl _)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
