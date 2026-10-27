module

import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.RankThree.PartTwo.Sec17.Proof176Steps

@[expose] def KFact76 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → CFSG.pPrimeCore 3 Y = ⊥ →
    ∀ A : Subgroup Y, Nat.card A = 3 →
      (∀ g : Y, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set Y) →
        A.map (MulAut.conj g).toMonoidHom = A) →
      IsSimpleGroup ↥(Subgroup.normalClosure (A : Set Y)) ∧
        (CFSG.Open.pRank 3 (Subgroup.normalClosure (A : Set Y)) = 1 ∨
          (∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.G2 q).Valid, q.p ≠ 3 ∧
            Nonempty (↥(Subgroup.normalClosure (A : Set Y)) ≃*
              (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)) ∨
          (∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid,
            q.card = 3 ∧ Nonempty (↥(Subgroup.normalClosure (A : Set Y)) ≃*
              (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)) ∨
          Nonempty (↥(Subgroup.normalClosure (A : Set Y)) ≃*
            (TauCeti.CFSGIndex.sporadic .J2).Group))

@[expose] def KFactG2NormalizerMax : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    (∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.G2 q).Valid, q.p ≠ 3 ∧
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)) →
    ∀ A : Subgroup K, Nat.card A = 3 →
      (∀ g : K, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set K) →
        A.map (MulAut.conj g).toMonoidHom = A) →
      IsCoatom (Subgroup.normalizer (A : Set K))

@[expose] def KFactU33J2NormalizerMax : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    ((∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid,
        q.card = 3 ∧ Nonempty (K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)) ∨
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J2).Group)) →
    ∀ A : Subgroup K, Nat.card A = 3 →
      (∀ g : K, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set K) →
        A.map (MulAut.conj g).toMonoidHom = A) →
      IsCoatom (Subgroup.normalizer (A : Set K))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
