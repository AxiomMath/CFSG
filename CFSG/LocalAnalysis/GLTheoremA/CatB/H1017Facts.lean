module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8

@[expose] def TwoRankLe (p : ℕ) (s : TauCeti.SporadicName) (k : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K (sporIs s) → GLATwoLocalRank p K ≤ k

@[expose] def I1016LyFact : Prop := TwoRankLe 3 .Ly 3

@[expose] def I1016Co2Fact : Prop := TwoRankLe 3 .Co2 3

@[expose] def I1016Co1Fact : Prop := TwoRankLe 3 .Co1 4

@[expose] def I1016Fi24Fact : Prop := TwoRankLe 3 .Fi24Prime 5

@[expose] def I1016SuzFact : Prop := TwoRankLe 3 .Suz 3

@[expose] def I1016ThFact : Prop := TwoRankLe 3 .Th 3

@[expose] def I1016M3Fact : Prop := TwoRankLe 3 .M 6

@[expose] def I1016M5Fact : Prop := TwoRankLe 5 .M 3

@[expose] def RowTwoRankFact (row : Row) : Prop :=
  TwoRankLe row.prime row.name (row.rank - 1)

@[expose] def I1016RowFacts : Prop := ∀ row : Row, RowTwoRankFact row

theorem i1016RowFacts_of_named (hLy : I1016LyFact) (hCo2 : I1016Co2Fact) (hCo1 : I1016Co1Fact)
    (hFi24 : I1016Fi24Fact) (hSuz : I1016SuzFact) (hTh : I1016ThFact) (hM3 : I1016M3Fact)
    (hM5 : I1016M5Fact) : I1016RowFacts := by
  intro row
  cases row
  · exact hLy
  · exact hCo2
  · exact hCo1
  · exact hFi24
  · exact hFi24
  · exact hSuz
  · exact hSuz
  · exact hTh
  · exact hM3
  · exact hM5

@[expose] def sporIn (S : List TauCeti.SporadicName) : TauCeti.CFSGIndex → Prop :=
  fun i => ∃ s ∈ S, i = TauCeti.CFSGIndex.sporadic s

@[expose] def I1017TableFact : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → p ≠ 2 → catalogIs K isSporIndex →
    3 ≤ GLATwoLocalRank p K →
      (p = 3 ∧ catalogIs K (sporIn [.ONan, .HN, .Ly, .Co1, .Co2, .Co3, .Fi22, .Fi23, .Fi24Prime,
        .B, .Th, .M, .Suz])) ∨ (p = 5 ∧ catalogIs K (sporIs .M))

@[expose] def NoTwistRank (s : TauCeti.SporadicName) (r : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K (sporIs s) → ∀ E : Subgroup K,
    IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E → ∀ T : Subgroup K, IsPGroup 2 T →
      E ≤ Subgroup.normalizer (T : Set K) → ∀ e ∈ E, ∀ t ∈ T, e * t = t * e

@[expose] def I1017CoThreeTwist : Prop := NoTwistRank .Co3 3

@[expose] def I1017FiTwoTwoTwist : Prop := NoTwistRank .Fi22 4

@[expose] def I1017FiTwoThreeTwist : Prop := NoTwistRank .Fi23 5

@[expose] def I1017BabyTwist : Prop := NoTwistRank .B 5

@[expose] def TwoRankAttained (p : ℕ) (s : TauCeti.SporadicName) (r : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K (sporIs s) → ∃ E T : Subgroup K,
    IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set K)

@[expose] def I1017FiTwoTwoAttained : Prop := TwoRankAttained 3 .Fi22 4

@[expose] def I1017FiTwoThreeAttained : Prop := TwoRankAttained 3 .Fi23 5

@[expose] def I1017BabyAttained : Prop := TwoRankAttained 3 .B 5

@[expose] def I1017CoverFiTwoTwo : Prop :=
  ∀ (H : Type) [Group H] [Finite H], catalogIs (H ⧸ Subgroup.center H) (sporIs .Fi22) →
    Nat.card (Subgroup.center H) = 3 → ∃ E T : Subgroup H, IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 5 ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set H)

@[expose] def SimpleElemRank (p : ℕ) (s : TauCeti.SporadicName) (r : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K (sporIs s) → ∃ E : Subgroup K,
    IsElemAbelian p E ∧ Nat.card E = p ^ r

@[expose] def CoverElemRank (s : TauCeti.SporadicName) (r : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], catalogIs (H ⧸ Subgroup.center H) (sporIs s) →
    Nat.card (Subgroup.center H) = 3 → ∃ E : Subgroup H, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r

@[expose] def I1017LyRank : Prop := SimpleElemRank 3 .Ly 4
@[expose] def I1017CoTwoRank : Prop := SimpleElemRank 3 .Co2 4
@[expose] def I1017CoOneRank : Prop := SimpleElemRank 3 .Co1 5
@[expose] def I1017FiTwoFourRank : Prop := SimpleElemRank 3 .Fi24Prime 6
@[expose] def I1017SuzRank : Prop := SimpleElemRank 3 .Suz 4
@[expose] def I1017ThRank : Prop := SimpleElemRank 3 .Th 4
@[expose] def I1017MonsterThreeRank : Prop := SimpleElemRank 3 .M 7
@[expose] def I1017MonsterFiveRank : Prop := SimpleElemRank 5 .M 4
@[expose] def I1017FiTwoFourCoverRank : Prop := CoverElemRank .Fi24Prime 7
@[expose] def I1017SuzCoverRank : Prop := CoverElemRank .Suz 5

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
