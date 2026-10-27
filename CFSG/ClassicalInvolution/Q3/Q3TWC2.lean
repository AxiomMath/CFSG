module

public import CFSG.ClassicalInvolution.Q3.Q3TWC1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWC

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open scoped MatrixGroups


@[expose] def PartnerPatternStmtB3 (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .POmegaOdd m) (conjClass3 K) z →
      ∀ β ∈ conjClass3 K, ∀ t : G, IsClassicalMember3 β t →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) →
        HasFixedMember (conjClass3 K) K β z → PartnerPatternBPair3 m (conjClass3 K) K β t

theorem chainPiece3TwinBPair_of_pattern (h3 : OddThreeFreeInput)
    (hpat : ∀ m, 3 ≤ m → PartnerPatternStmtB3 m) : Q3TW.ChainPiece3TwinBPair := by
  intro G _ _ _ hnab K z hR N hN hshape
  have hm : 3 ≤ N - 2 := by omega
  have hadm : StatedLieAdmissible .POmegaOdd (N - 2) 3 1 :=
    ⟨Nat.prime_three, le_rfl, hm, by norm_num⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_odd hm hadm) h3 hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ :=
    c.exists_partner hsingle (nonempty_fund_odd (p := 3) (f := 1) hm)
  obtain ⟨ι, hι, D, hcard, -⟩ := id hshape
  exact chain_of_patternB3 (Gaps.fundNoncentral 3) hN c hsingle D hβ ht hKβ
    (hpat (N - 2) hm G hnab K z hR hshape β hβ t ht hKβ hfix)

end CFSG.ClassicalInvolution.Q3.Q3TWC
