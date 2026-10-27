module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846f
public import CFSG.Quasithin.Background.C2Basic

public section

namespace CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem perfectCore_sup_pCoreOf_eq {L N : Subgroup G} (hLN : L ≤ N)
    (hsub : CFSG.Open.IsSubnormal L N) (hperf : ⁅L, L⁆ = L) :
    CFSG.Quasithin.perfectCore (L ⊔ CFSG.Open.pCoreOf 2 N) = L := by
  have hAp : ⁅L.subgroupOf N, L.subgroupOf N⁆ = L.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator]
    simp only [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLN, hperf]
  have hsnTop : CFSG.Open.IsSubnormal (L.subgroupOf N) ⊤ :=
    CFSG.Quasithin.A3.subnormal_top_iff.mpr
      ((CFSG.Quasithin.isSubnormal_iff_subgroupOf hLN).mp hsub)
  have hP := CFSG.LocalAnalysis.UniquenessCase.UC6S846.perfectCore_sup_eq (Y := ↥N)
    (A := L.subgroupOf N) (Q := CFSG.pCore 2 ↥N) (CFSG.pCore_isPGroup) hsnTop hAp
  have hmap := congrArg (Subgroup.map N.subtype) hP
  rw [CFSG.Quasithin.map_perfectCore N.subtype, Subgroup.map_sup,
    Subgroup.subgroupOf_map_subtype L N, inf_eq_left.mpr hLN,
    show (CFSG.pCore 2 ↥N).map N.subtype = CFSG.Open.pCoreOf 2 N from rfl] at hmap
  exact hmap

end CFSG.GroupTheory

end
