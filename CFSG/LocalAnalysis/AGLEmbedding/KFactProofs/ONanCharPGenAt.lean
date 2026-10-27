module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def CharPGenAt (Fam : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Fam d → Nonempty (K ≃* CatGroup d) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic → ¬ IsRankOneLieIndex d.1 →
        ∀ T : Sylow p K, GLBCore p 1 (T : Subgroup K) = ⊤

theorem charPGenAt_or {F₁ F₂ : TauCeti.ValidLieTypeIndex → Prop} (h₁ : CharPGenAt F₁)
    (h₂ : CharPGenAt F₂) : CharPGenAt fun d => F₁ d ∨ F₂ d :=
  fun K _ _ hs hn d hd => hd.elim (h₁ K hs hn d) (h₂ K hs hn d)

theorem charPGen_of_charPGenAt {Fam : TauCeti.ValidLieTypeIndex → Prop} (h : CharPGenAt Fam)
    (hcover : ∀ d : TauCeti.ValidLieTypeIndex, ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic →
      ¬ IsRankOneLieIndex d.1 → Fam d) : CharPGen :=
  fun K _ _ hs hn d hd p hp hp2 hchar hr =>
    h K hs hn d (hcover d p hp hp2 hchar hr) hd p hp hp2 hchar hr

theorem charPGenAt_of_pGroup {Fam : TauCeti.ValidLieTypeIndex → Prop}
    (h : ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), Fam d →
      K ≃* CatGroup d → ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic →
        ¬ IsRankOneLieIndex d.1 → ∃ P : Subgroup K, IsPGroup p P ∧ GLBCore p 1 P = ⊤) :
    CharPGenAt Fam := by
  intro K _ _ _ _ d hd ⟨e⟩ p hp hp2 hchar hr T
  obtain ⟨P, hP, hcore⟩ := h K d hd e p hp hp2 hchar hr
  exact CFSG.AGLEmbeddingD2.glbCore_eq_top_of_pGroup hp 1 hP hcore T

end CFSG.AGLEmbedding
