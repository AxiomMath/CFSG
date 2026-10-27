module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbedding

@[expose] def HyperGen (p : ℕ) {Y : Type*} [Group Y] (K E : Subgroup Y) : Prop :=
  K ≤ Subgroup.closure {k : Y | k ∈ K ∧ ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = p ∧
    ∀ f ∈ F, f * k = k * f}

@[expose] def SeitzHyperInnerFor (Fam : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K E : Subgroup Y), K.Normal →
    Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex, Fam d →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ P1ThreeLieList p d → IsElemAbelian p E → Nat.card E = p ^ 3 →
    (∀ c ∈ E ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) →
    E ≤ K ⊔ Subgroup.centralizer (K : Set Y) → HyperGen p K E

end CFSG.LieType.SeitzGeneration
