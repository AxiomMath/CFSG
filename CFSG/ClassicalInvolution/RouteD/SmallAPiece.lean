module

public import CFSG.ClassicalInvolution.RouteD.SmallAMain
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_chain_of_setup (hMFZ : Gaps.FundNoncentral p) {K : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) {m : ℕ} (h3 : 3 ≤ m) (h4 : m ≤ 4)
    (hshape : LocalShapeA p f m (conjClass K) z) :
    ∃ U : Fin (m + 2) → Subgroup G, (∀ i, U i ∈ conjClass K) ∧
      (∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
      ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j) := by
  obtain rfl | rfl : m = 3 ∨ m = 4 := by omega
  · exact exists_chain_three hMFZ S.odd S.five S.inClass S.exact (mem_conjClass_self K)
      (single_class K) S.cls hshape S.p1
  · exact exists_chain_four hMFZ S.odd S.five S.inClass S.exact (mem_conjClass_self K)
      (single_class K) S.cls hshape S.p1

end CFSG.ClassicalInvolution.Generic.CoreAssembly
