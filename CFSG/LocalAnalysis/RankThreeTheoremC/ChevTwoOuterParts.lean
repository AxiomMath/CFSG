module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.AGLEmbedding (IsChevTwoOuterIndex KFactChevTwoOuterGen)

@[expose] def IsChevTwoOuter3D42Index (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .trialityD4 q

@[expose] def IsChevTwoOuter3D48Index (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .trialityD4 q

@[expose] def IsChevTwoOuterU38Index (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .twistedA 2 q

theorem isChevTwoOuterIndex_iff (d : TauCeti.ValidLieTypeIndex) :
    IsChevTwoOuterIndex d ↔ IsChevTwoOuter3D42Index d ∨ IsChevTwoOuter3D48Index d ∨
      IsChevTwoOuterU38Index d := by
  constructor
  · rintro (⟨q, hq, he, hd⟩ | ⟨q, hq, he, hd | hd⟩)
    · exact Or.inl ⟨q, hq, he, hd⟩
    · exact Or.inr (Or.inl ⟨q, hq, he, hd⟩)
    · exact Or.inr (Or.inr ⟨q, hq, he, hd⟩)
  · rintro (⟨q, hq, he, hd⟩ | ⟨q, hq, he, hd⟩ | ⟨q, hq, he, hd⟩)
    · exact Or.inl ⟨q, hq, he, hd⟩
    · exact Or.inr ⟨q, hq, he, Or.inl hd⟩
    · exact Or.inr ⟨q, hq, he, Or.inr hd⟩

@[expose] def KFactChevTwoOuterNormal : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoOuterIndex d →
    ∀ S : Sylow 3 (Outer (TauCeti.CFSGIndex.lie d).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie d).Group)).Normal

@[expose] def ChevTwoOuterGenAt (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → Open.IsQuasisimple K →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    IsPGroup 3 (Subgroup.centralizer (K : Set X)) →
    (∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype) →
    ∀ R : Sylow 3 X, 3 ≤ Open.pRank 3 (R : Subgroup X) →
      K ≤ GLBWeakCore 3 (R : Subgroup X)

@[expose] def KFactChevTwoOuterGen3D42 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoOuter3D42Index d → ChevTwoOuterGenAt d

@[expose] def KFactChevTwoOuterGen3D48 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoOuter3D48Index d → ChevTwoOuterGenAt d

@[expose] def KFactChevTwoOuterGenU38 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoOuterU38Index d → ChevTwoOuterGenAt d

theorem kFactChevTwoOuterGen_of_parts (h1 : KFactChevTwoOuterNormal)
    (h2 : KFactChevTwoOuterGen3D42) (h3 : KFactChevTwoOuterGen3D48)
    (h4 : KFactChevTwoOuterGenU38) : KFactChevTwoOuterGen := by
  refine ⟨h1, fun d hd => ?_⟩
  rcases (isChevTwoOuterIndex_iff d).mp hd with h | h | h
  · exact h2 d h
  · exact h3 d h
  · exact h4 d h

end CFSG.LocalAnalysis.RankThreeTheoremC
