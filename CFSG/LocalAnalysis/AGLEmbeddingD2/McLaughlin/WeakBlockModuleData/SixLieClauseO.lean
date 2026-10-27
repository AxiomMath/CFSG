module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOutUnitary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOutOrth
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthogonalRank
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

theorem autThreePowInner_of_isFiveList {X : Type} [Group X] (h : IsFiveList X) :
    AutThreePowInner X := by
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ := h
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  obtain ⟨hp, hf⟩ := primePower_card_two' hq
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hp
      (by norm_num) e
    rw [hp, hf] at h
    exact autThreePowInner_psp_two le_rfl h
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 q hv hp
      (by norm_num) e
    rw [hp, hf] at h
    exact autThreePowInner_psp_two (by norm_num) h
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hv hp e
    rw [hp, hf] at h
    exact autThreePowInner_pomegaMinus_two le_rfl h
  · have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    rw [hp, hf] at h
    exact autThreePowInner_psu_two (n := 3 + 1) (by norm_num) (by norm_num) h
  · have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 q hv e
    rw [hp, hf] at h
    exact autThreePowInner_psu_two (n := 4 + 1) (by norm_num) (by norm_num) h

theorem clauseO_of_isFiveList {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    (hL : IsWeakSBlock M S L) (h : IsFiveList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) :
    ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      IsPGroup 3 (Subgroup.zpowers u) →
        u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  clauseO_of_cover hL.le hL.perfect (autThreePowInner_of_isFiveList h) (MulEquiv.refl _)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
