module

public import CFSG.ClassicalInvolution.WeakCT.DLWeakAgree
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.RouteD.LocalTwinSp
public import CFSG.LieType.Universal.Spin.Datum

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)

@[expose] def WeakCT3OddMapPair (N : ℕ) : Prop :=
  ∀ {G : Type} [Group G] (U : Fin N → Subgroup G),
    (∀ i j : Fin N, i.val + 1 < j.val → Commutes (U i) (U j)) →
    (∀ i j : Fin N, i.val + 1 = j.val → j.val + 1 < N →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) →
    (∀ i j : Fin N, i.val + 2 = N → j.val + 1 = N →
      ∃ W, SymplecticBlockPair (GaloisField 3 1) W (U i) (U j)) →
    ∃ Ψ : spinGroup (quadOdd N (GaloisField 3 1)) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k : Fin N, (rankOne (oddDatum N (GaloisField 3 1)).rootGroup k).map Ψ = U k

end CFSG.ClassicalInvolution.Q3.Q3TW
