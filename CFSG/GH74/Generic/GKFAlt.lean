module

public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.GH74.Generic

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial

theorem alt_cover_of_central_kernel {n : ℕ} (hn : 5 ≤ n) {K : Type} [Group K] [Finite K]
    (hK : IsQuasisimple K) (h2 : IsPGroup 2 ↥(center K))
    (e : K ⧸ center K ≃* alternatingGroup (Fin n)) : Nat.card (center K) ≤ 2 := by
  have hperf : Group.IsPerfect K := hK.1
  have h := alternating_perfect_central_two_kernel_order_at_most_two
    hn (centralQuotientMap e) (centralQuotientMap_surjective e) (centralQuotientMap_ker e).le
    (by rw [centralQuotientMap_ker e]; exact h2)
  rwa [centralQuotientMap_ker e] at h

end CFSG.GH74.Generic
