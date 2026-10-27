module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeList

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

@[expose] def SignalizerThreeOn (p : ℕ) (K : Type*) [Group K] [Finite K] : Prop :=
  ∀ T : Sylow p K, ∀ W : Subgroup (MulAut K), IsPGroup 3 W →
    (∀ g ∈ (T : Subgroup K), ∀ w ∈ W, MulAut.conj g * w * (MulAut.conj g)⁻¹ ∈ W) → W = ⊥

@[expose] def SignalizerThreeAt (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* X) → SignalizerThreeOn p K

@[expose] def KFactNineThreeSignalizerThree : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ (K : Type) [Group K] [Finite K],
    NineThreeListGroup p K → SignalizerThreeOn p K

@[expose] def SignalizerThreeLinTwo : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex),
    q.p = p → 2 ≤ q.exponent → d.1 = .A 1 q → SignalizerThreeAt p (TauCeti.CFSGIndex.lie d).Group

@[expose] def SignalizerThreeUnitary : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex),
    q.p = p → d.1 = .twistedA 2 q → SignalizerThreeAt p (TauCeti.CFSGIndex.lie d).Group

@[expose] def SignalizerThreeSpFour : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex),
    q.p = p → q.exponent = 1 → d.1 = .B 2 q → SignalizerThreeAt p (TauCeti.CFSGIndex.lie d).Group

@[expose] def SignalizerThreeLinThree : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex),
    q.p = p → q.exponent = 1 → d.1 = .A 2 q → SignalizerThreeAt p (TauCeti.CFSGIndex.lie d).Group

@[expose] def SignalizerThreeLieFive : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (d.1 = .suzuki 2 ∨ d.1 = .tits ∨ d.1 = .reeF4 2) →
    SignalizerThreeAt 5 (TauCeti.CFSGIndex.lie d).Group

@[expose] def SignalizerThreeAltTen : Prop :=
  ∀ h : 5 ≤ 10, SignalizerThreeAt 5 (TauCeti.CFSGIndex.alternating 10 h).Group

@[expose] def SignalizerThreeSporadic : Prop :=
  (∀ s : TauCeti.SporadicName, (s = .McL ∨ s = .HS ∨ s = .Ru) →
      SignalizerThreeAt 5 (TauCeti.CFSGIndex.sporadic s).Group) ∧
    (∀ s : TauCeti.SporadicName, (s = .ONan ∨ s = .Fi24Prime ∨ s = .He) →
      SignalizerThreeAt 7 (TauCeti.CFSGIndex.sporadic s).Group) ∧
    SignalizerThreeAt 11 (TauCeti.CFSGIndex.sporadic .J4).Group

@[expose] def SignalizerThreeSzSq : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
    SignalizerThreeAt 5 ((TauCeti.CFSGIndex.lie d).Group × (TauCeti.CFSGIndex.lie d).Group)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
