module

public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen
public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.OddCore

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

variable {G : Type} [Group G] [Finite G]

@[expose] def KFact76Max : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → CFSG.pPrimeCore 3 Y = ⊥ →
    ∀ A : Subgroup Y, Nat.card A = 3 →
      (∀ g : Y, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set Y) →
        A.map (MulAut.conj g).toMonoidHom = A) →
      IsSimpleGroup ↥(Subgroup.normalClosure (A : Set Y)) ∧
        (CFSG.Open.pRank 3 (Subgroup.normalClosure (A : Set Y)) = 1 ∨
          ∀ W : Subgroup Y,
            Subgroup.normalizer (A : Set Y) ⊓ Subgroup.normalClosure (A : Set Y) ≤ W →
            W ≤ Subgroup.normalClosure (A : Set Y) →
            W = Subgroup.normalizer (A : Set Y) ⊓ Subgroup.normalClosure (A : Set Y) ∨
              W = Subgroup.normalClosure (A : Set Y))

@[expose] def KFactFi22SPEThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.pPrimeCore 5 X = ⊥ →
    CFSG.AGLEmbedding.IsFi22 ↥(CFSG.generalizedFitting X) →
    ∀ N : Subgroup X, CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N →
      2 ≤ CFSG.Open.pRank 3 N

@[expose] def KFactFieldAutThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    ∀ L : Subgroup X, CFSG.IsComponent L → L.Normal → CFSG.Open.pRank 3 L = 1 →
      ∀ a : X, orderOf a = 3 → a ∉ L ⊔ Subgroup.centralizer (L : Set X) →
        ∀ P : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 P L →
          a ∈ Subgroup.normalizer (P : Set X) → ∃ x ∈ P, a * x ≠ x * a

@[expose] def StronglyEmbeddedSolvableId : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore p X = ⊥ →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
      ∀ N : Subgroup X, CFSG.RankThree.PartOne.IsStronglyPEmbedded p N →
        IsSolvable ↥N ∨
          (2 ≤ CFSG.Open.pRank 3 N ∧
            (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CoverHasLargeTwoLocal
                ↥(CFSG.generalizedFitting X) ∨
              (p = 5 ∧
                Nonempty (↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin 10)))))

structure S8Core (G : Type) [Group G] [Finite G] where
  cstar : CStarGen G
  M : Subgroup G
  maxLocal : CFSG.Open.rankThreeIsMaxTwoLocal M
  q : ℕ
  hq : q ∈ sigmaSet G M
  strong : ∀ r ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded r M

namespace S8Core

structure Config (k : S8Core G) (H : Subgroup G) : Prop where
  ne_top : H ≠ ⊤
  not_le : ¬ H ≤ k.M
  two_le_pRank : 2 ≤ CFSG.Open.pRank k.q (H ⊓ k.M)

theorem prime (k : S8Core G) : k.q.Prime :=
  CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime k.q k.hq.1

theorem strongQ (k : S8Core G) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded k.q k.M :=
  k.strong k.q k.hq

theorem M_ne_top (k : S8Core G) : k.M ≠ ⊤ := by
  haveI := k.cstar.simple
  exact CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top k.cstar.nonab k.M k.maxLocal.1

theorem huniq (k : S8Core G) :
    ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank k.q (Subgroup.normalizer (D : Set G) ⊓ k.M) →
      Subgroup.normalizer (D : Set G) ≤ k.M := by
  intro D hDne hD2 hrank
  have hq := k.prime
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hq.one_lt (Subgroup.normalizer (D : Set G) ⊓ k.M)
  have hEr : 2 ≤ CFSG.Open.pRank k.q E :=
    hrank.trans (CFSG.SectionRank.le_pRank hq.one_lt le_rfl hEel hEcard)
  exact k.cstar.embed k.q k.hq.1 k.M k.maxLocal E (hE.trans inf_le_right)
    (CFSG.Open.IsElemAbelian.isPGroup hEel) hEr (Subgroup.normalizer (D : Set G))
    ⟨D, hDne, hD2, rfl⟩ (hE.trans inf_le_left)

theorem pPrimeCore_le (k : S8Core G) {H : Subgroup G} (hH : k.Config H) :
    (CFSG.pPrimeCore k.q ↥H).map H.subtype ≤ k.M :=
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.pPrimeCore_le k.strongQ k.prime
    hH.two_le_pRank

theorem odd_card_pPrimeCore (k : S8Core G) {H : Subgroup G} (hH : k.Config H) :
    Odd (Nat.card (CFSG.pPrimeCore k.q ↥H)) :=
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.odd_card_pPrimeCore k.strongQ k.prime
    k.huniq hH.not_le hH.two_le_pRank

@[expose] def ofGen (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) {q : ℕ} (hq : q ∈ sigmaSet G M)
    (hs : ∀ r ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded r M) : S8Core G :=
  ⟨hC, M, hM, q, hq, hs⟩

end S8Core

structure Hyp83 (M H L A : Subgroup G) : Prop where
  twoLocal : CFSG.Open.IsTwoLocal H
  le : L ≤ H ⊓ M
  comp : CFSG.IsPComponent 3 (L.subgroupOf (H ⊓ M))
  rank : CFSG.Open.pRank 3 L = 1
  le_L : A ≤ L
  card : Nat.card A = 3
  unique : A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M
  weak : ∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≤
      Subgroup.normalizer (A : Set G) ⊓ (H ⊓ M) →
    A.map (MulAut.conj h).toMonoidHom = A

namespace Hyp83

theorem mk_of_args {M : Subgroup G} (H : Subgroup G) (hH : CFSG.Open.IsTwoLocal H)
    (L : Subgroup G) (hL : L ≤ H ⊓ M) (hcomp : CFSG.IsPComponent 3 (L.subgroupOf (H ⊓ M)))
    (hrank : CFSG.Open.pRank 3 L = 1) (A : Subgroup G) (hA : A ≤ L)
    (hcard : Nat.card A = 3) (huniq : A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M)
    (hweak : ∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≤
        Subgroup.normalizer (A : Set G) ⊓ (H ⊓ M) →
      A.map (MulAut.conj h).toMonoidHom = A) : Hyp83 M H L A :=
  ⟨hH, hL, hcomp, hrank, hA, hcard, huniq, hweak⟩

end Hyp83

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
