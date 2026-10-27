module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross

public section

namespace GL83.I243

open CFSG

@[expose] def IsThreeCoverIndex (i : TauCeti.CFSGIndex) : Prop :=
  i = .sporadic .McL ∨ i = .sporadic .Suz ∨ i = .sporadic .Fi22 ∨ i = .sporadic .Fi24Prime ∨
  i = .sporadic .J3 ∨ i = .sporadic .ONan ∨
  (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid), q.card = 3 ∧
      i = .lie ⟨.twistedA 3 q, hv⟩) ∨
  (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 3 q).Valid), q.card = 3 ∧
      i = .lie ⟨.B 3 q, hv⟩) ∨
  (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.card = 3 ∧
      i = .lie ⟨.G2 q, hv⟩)

@[expose] def IsThreeSmallIndex (i : TauCeti.CFSGIndex) : Prop :=
  (∃ (n : ℕ) (hn : 5 ≤ n), (n = 6 ∨ n = 7) ∧ i = .alternating n hn) ∨ i = .sporadic .M22

@[expose] def IsThreeLFourIndex (i : TauCeti.CFSGIndex) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧
    ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q

@[expose] def IsPCoverLieIndex (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ (r : ℕ) (q : TauCeti.PrimePower), d = .A r q ∧ p ∣ q.card - 1) ∨
    (∃ (r : ℕ) (q : TauCeti.PrimePower), d = .twistedA r q ∧ p ∣ q.card + 1) ∨
    (p = 3 ∧ ((∃ q : TauCeti.PrimePower, d = .E6 q) ∨
      (∃ q : TauCeti.PrimePower, d = .twistedE6 q)))

@[expose] def PCoverList : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    p ∣ Nat.card (Subgroup.center K) → ∀ i : TauCeti.CFSGIndex,
      Nonempty (K ⧸ Subgroup.center K ≃* i.Group) →
      ((∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ p ≠ d.1.characteristic ∧
          ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1 ∧ IsPCoverLieIndex p d.1) ∨
        (p = 3 ∧ (IsThreeCoverIndex i ∨
          ((IsThreeSmallIndex i ∨ IsThreeLFourIndex i) ∧
            ¬ 3 ^ 2 ∣ Nat.card (Subgroup.center K)))))

end GL83.I243
