module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisAutChain
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding

@[expose] def OddRankLeThree (L : Type*) [Group L] : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ A : Subgroup L, IsMulCommutative A → (∀ x ∈ A, x ^ q = 1) →
    Nat.card A ≤ q ^ 3

@[expose] def HeisCoreOn (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L → Odd (Nat.card (Subgroup.center L)) →
    OddRankLeThree L → IsSimpleGroup (L ⧸ Subgroup.center L) →
    ∀ (d : TauCeti.ValidLieTypeIndex), P d.1 →
    (L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ p : ℕ, p.Prime → 5 ≤ p →
      NoHeisAut p (L ⧸ Subgroup.center L) ∨
        (p = 5 ∧ Subgroup.center L = ⊥ ∧
          ∃ q : TauCeti.PrimePower, d.1 = .twistedA 4 q ∧ q.card = 4)

@[expose] def HeisCoreAlt : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L → OddRankLeThree L → ∀ k : ℕ, 5 ≤ k →
    (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin k)) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → NoHeisAut p (L ⧸ Subgroup.center L)

@[expose] def HeisCoreSmall : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L → ∀ d : TauCeti.ValidLieTypeIndex,
    ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) →
    (L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → NoHeisAut p (L ⧸ Subgroup.center L)

@[expose] def PSU54ParabolicFive : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    Subgroup.center ↥L = ⊥ → ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    d.1 = .twistedA 4 q → q.card = 4 →
    (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    5 ∣ (P.subgroupOf L).index ∧ ¬ 5 ^ 3 ∣ Nat.card P

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
