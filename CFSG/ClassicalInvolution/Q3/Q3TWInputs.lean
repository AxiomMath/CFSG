module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinBModel
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDWeak

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)

section Odd

@[expose] def WeakCT3OddMap (N : ℕ) : Prop :=
  ∀ {G : Type} [Group G] (U : Fin N → Subgroup G),
    (∀ i j : Fin N, i.val + 1 < j.val → Commutes (U i) (U j)) →
    (∀ i j : Fin N, i.val + 1 = j.val → j.val + 1 < N →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) →
    (∀ i j : Fin N, i.val + 2 = N → j.val + 1 = N →
      ∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)) →
    ∃ Ψ : spinGroup (quadOdd N (GaloisField 3 1)) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      ∀ k : Fin N, (rankOne (oddDatum N (GaloisField 3 1)).rootGroup k).map Ψ = U k

@[expose] def LeviEmbed3Odd : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n),
    ∃ Θ : spinGroup (quadOdd (n - 2) (GaloisField 3 1)) →* spinGroup (quadOdd n (GaloisField 3 1)),
      Θ.ker ≤ Subgroup.center _ ∧
      (∀ k : Fin (n - 2), (rankOne (oddDatum (n - 2) (GaloisField 3 1)).rootGroup k).map Θ =
        rankOne (oddDatum n (GaloisField 3 1)).rootGroup (nodeB (n := n) (by omega) k)) ∧
      Θ.range = ⨆ k : Fin (n - 2),
        rankOne (oddDatum n (GaloisField 3 1)).rootGroup (nodeB (n := n) (by omega) k)

end Odd

section Minus

@[expose] def nodeMinus {n : ℕ} (hn : 4 ≤ n) (k : Fin (n - 2 - 1)) : Fin (n - 1) :=
  ⟨k.val + 2, by have := k.isLt; omega⟩


@[expose] def WeakCT3MinusMap (N : ℕ) : Prop :=
  ∀ {G : Type} [Group G] (U : Fin (N - 1) → Subgroup G),
    (∀ i j : Fin (N - 1), i.val + 1 < j.val → Commutes (U i) (U j)) →
    (∀ i j : Fin (N - 1), i.val + 1 = j.val → j.val + 2 < N →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) →
    (∀ i j : Fin (N - 1), i.val + 3 = N → j.val + 2 = N →
      ∃ W, Models.TwistedPairs.TwistedB2BlockPair (minusCoeffs_irr 3 1) W (U i) (U j)) →
    ∃ Ψ : spinGroup (quadMinus N (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) →* G,
      Ψ.ker ≤ Subgroup.center _ ∧
      ∀ k : Fin (N - 1),
        (rankOne (Twisted.minusDatum N (minusCoeffs_irr 3 1)).rootGroup k).map Ψ = U k

@[expose] def LeviEmbed3Minus : Prop :=
  ∀ (n : ℕ) (hn : 6 ≤ n),
    ∃ Θ : spinGroup (quadMinus (n - 2) (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) →*
      spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
      Θ.ker ≤ Subgroup.center _ ∧
      (∀ k : Fin (n - 2 - 1), (rankOne (Twisted.minusDatum (n - 2) (minusCoeffs_irr 3 1)).rootGroup
          k).map Θ = rankOne (Twisted.minusDatum n (minusCoeffs_irr 3 1)).rootGroup
          (nodeMinus (by omega) k)) ∧
      Θ.range = ⨆ k : Fin (n - 2 - 1),
        rankOne (Twisted.minusDatum n (minusCoeffs_irr 3 1)).rootGroup (nodeMinus (by omega) k)

end Minus

end CFSG.ClassicalInvolution.Q3.Q3TW
