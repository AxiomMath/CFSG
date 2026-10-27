module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314

open CFSG.Open

@[expose] def CharPGen2At (Fam : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    ∀ d : TauCeti.ValidLieTypeIndex, Fam d → Nonempty (K ≃* CFSG.AGLEmbedding.CatGroup d) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic →
        ∀ T : Sylow p K, GLBCore p 2 (T : Subgroup K) = ⊤

theorem charPGen2At_or {F₁ F₂ : TauCeti.ValidLieTypeIndex → Prop} (h₁ : CharPGen2At F₁)
    (h₂ : CharPGen2At F₂) : CharPGen2At fun d => F₁ d ∨ F₂ d :=
  fun K _ _ hs d hd => hd.elim (h₁ K hs d) (h₂ K hs d)

theorem charPGen2At_of_pGroup {Fam : TauCeti.ValidLieTypeIndex → Prop}
    (h : ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), Fam d →
      K ≃* CFSG.AGLEmbedding.CatGroup d → ∀ p : ℕ, p.Prime → p ≠ 2 →
        p = d.1.characteristic → ∃ P : Subgroup K, IsPGroup p P ∧ GLBCore p 2 P = ⊤) :
    CharPGen2At Fam := by
  intro K _ _ _ d hd ⟨e⟩ p hp hp2 hchar T
  obtain ⟨P, hP, hcore⟩ := h K d hd e p hp hp2 hchar
  exact CFSG.AGLEmbeddingD2.glbCore_eq_top_of_pGroup hp 2 hP hcore T

theorem charPGen2At_of_pGroup_simple {Fam : TauCeti.ValidLieTypeIndex → Prop}
    (h : ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K] (d : TauCeti.ValidLieTypeIndex),
      Fam d → K ≃* CFSG.AGLEmbedding.CatGroup d → ∀ p : ℕ, p.Prime → p ≠ 2 →
        p = d.1.characteristic → ∃ P : Subgroup K, IsPGroup p P ∧ GLBCore p 2 P = ⊤) :
    CharPGen2At Fam := by
  intro K _ _ _ d hd ⟨e⟩ p hp hp2 hchar T
  obtain ⟨P, hP, hcore⟩ := h K d hd e p hp hp2 hchar
  exact CFSG.AGLEmbeddingD2.glbCore_eq_top_of_pGroup hp 2 hP hcore T

@[expose] def CharPGen2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ≃* CFSG.AGLEmbedding.CatGroup d) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic →
        ¬ CFSG.AGLEmbedding.IsRankOneLieIndex d.1 →
          ∀ T : Sylow p K, GLBCore p 2 (T : Subgroup K) = ⊤

theorem charPGen2_of_charPGen2At {Fam : TauCeti.ValidLieTypeIndex → Prop} (h : CharPGen2At Fam)
    (hcover : ∀ d : TauCeti.ValidLieTypeIndex, ∀ p : ℕ, p.Prime → p ≠ 2 →
      p = d.1.characteristic → ¬ CFSG.AGLEmbedding.IsRankOneLieIndex d.1 → Fam d) :
    CharPGen2 :=
  fun K _ _ hs d hd p hp hp2 hchar hr => h K hs d (hcover d p hp hp2 hchar hr) hd p hp hp2 hchar

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314
