module

public import CFSG.Quasithin.Background.F9Comp

public section

namespace CFSG

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_eq_inf_pCoreOf_of_isSubnormal {K H : Subgroup G}
    (hsn : CFSG.Open.IsSubnormal K H) : pCoreOf 2 K = K ⊓ pCoreOf 2 H := by
  refine le_antisymm ?_ ?_
  · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
      (CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal hsn)
  · have hKH : K ≤ H := hsn.le
    have h2 : IsPGroup 2 ↥(K ⊓ pCoreOf 2 H) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right
    have hnorm : K ≤ Subgroup.normalizer (((K ⊓ pCoreOf 2 H) : Subgroup G) : Set G) := by
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
          (hKH hx)⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm h2

end CFSG
