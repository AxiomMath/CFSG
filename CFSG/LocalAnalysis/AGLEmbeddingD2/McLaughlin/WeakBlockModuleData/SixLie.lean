module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def IsOmegaEightPlus (X : Type) [Group X] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .D 4 q) ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsFiveList (X : Type) [Group X] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 2 ∧
      (d.1 = .B 3 q ∨ d.1 = .B 4 q ∨ d.1 = .twistedD 4 q ∨ d.1 = .twistedA 3 q ∨
        d.1 = .twistedA 4 q)) ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

theorem isOmegaEightPlus_or_isFiveList {X : Type} [Group X] (h : IsOneImageList X) :
    IsOmegaEightPlus X ∨ IsFiveList X := by
  obtain ⟨d, ⟨q, hq, hd⟩, he⟩ := h
  rcases hd with hd | hd | hd | hd | hd | hd
  · exact Or.inr ⟨d, ⟨q, hq, Or.inl hd⟩, he⟩
  · exact Or.inr ⟨d, ⟨q, hq, Or.inr (Or.inl hd)⟩, he⟩
  · exact Or.inl ⟨d, ⟨q, hq, hd⟩, he⟩
  · exact Or.inr ⟨d, ⟨q, hq, Or.inr (Or.inr (Or.inl hd))⟩, he⟩
  · exact Or.inr ⟨d, ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inl hd)))⟩, he⟩
  · exact Or.inr ⟨d, ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inr hd)))⟩, he⟩

@[expose] def KFactBlockSixLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeTwo M S L → BlockPLThreeSolv M S L →
    IsFiveList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) →
    (∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      IsPGroup 3 (Subgroup.zpowers u) →
        u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
    (Open.pRank 3 (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≤ 2 →
      ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        T ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → IsPGroup 3 T → IsElemAbelian 3 T) ∧
    (∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsElemAbelian 3 E → Nat.card E = 9 →
      E ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
      (∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        T ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → IsPGroup 3 T → Nat.card T ≤ 9) →
      ¬ IrreducibleOn
        (Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
          Subgroup.normalizer
            (barM M (Subgroup.normalizer (S : Set G) ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
          Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) E)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
