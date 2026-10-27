module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

@[expose] def IsLThreeTwo (X : Type) [Group X] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsDoublingList (X : Type) [Group X] : Prop :=
  IsLThreeTwo X ∨ Nonempty (X ≃* alternatingGroup (Fin 6)) ∨ IsUThreeThree X

@[expose] def IsOneImageList (X : Type) [Group X] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 2 ∧
      (d.1 = .B 3 q ∨ d.1 = .B 4 q ∨ d.1 = .D 4 q ∨ d.1 = .twistedD 4 q ∨
        d.1 = .twistedA 3 q ∨ d.1 = .twistedA 4 q)) ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsClassicalOverTwo (X : Type) [Group X] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2Index d.1 ∧ LieField d.1 = 2 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def CoveredByTwo {W : Type*} [Group W] (L S₀ A₁ A₂ : Subgroup W) : Prop :=
  ∀ P : Subgroup W, IsMinOverBorel L S₀ P →
    pElementSubgroup 2 P ≤ A₁ ∨ pElementSubgroup 2 P ≤ A₂

@[expose] def KFactParabolicCoverDoubling : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (L S₀ A₁ A₂ : Subgroup W), Open.IsQuasisimple ↥L →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsSylowTwoOf S₀ L →
    CoveredByTwo L S₀ A₁ A₂ →
    (3 ∣ Nat.card A₁ ∧ Open.pRank 3 A₁ ≤ 1 ∧ CFSG.HallHigman.IsPSolvable 3 ↥A₁) →
    (3 ∣ Nat.card A₂ ∧ Open.pRank 3 A₂ ≤ 1 ∧ CFSG.HallHigman.IsPSolvable 3 ↥A₂) →
    IsDoublingList (↥L ⧸ Subgroup.center ↥L)

@[expose] def KFactParabolicCoverOne : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (L S₀ A₁ A₂ : Subgroup W), Open.IsQuasisimple ↥L →
    IsClassicalOverTwo (↥L ⧸ Subgroup.center ↥L) → 3 ≤ Open.pRank 3 L →
    IsSylowTwoOf S₀ L → CoveredByTwo L S₀ A₁ A₂ →
    (Open.pRank 3 A₁ ≤ 2 ∧ (Open.pRank 3 A₁ = 2 → CFSG.HallHigman.IsPSolvable 3 ↥A₁)) →
    (Open.pRank 3 A₂ ≤ 2 ∧ (Open.pRank 3 A₂ = 2 → CFSG.HallHigman.IsPSolvable 3 ↥A₂)) →
    IsOneImageList (↥L ⧸ Subgroup.center ↥L)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
