module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63P_isComponentIn_of_subnormal {A N : Subgroup G} {w : G} {K : Subgroup G}
    (hAN : A ≤ N) (hsub : (A.subgroupOf N).IsSubnormal)
    (hK : IsComponentIn K (A ⊓ centralizer ({w} : Set G))) :
    IsComponentIn K (N ⊓ centralizer ({w} : Set G)) := by
  have hAB : A ⊓ centralizer ({w} : Set G) ≤ N ⊓ centralizer ({w} : Set G) :=
    inf_le_inf hAN le_rfl
  have hKB : K ≤ N ⊓ centralizer ({w} : Set G) := hK.le.trans hAB
  refine isComponentIn_of_subnormal hKB hK.isQuasisimple ?_
  have hKle : K.subgroupOf (N ⊓ centralizer ({w} : Set G)) ≤
      (A ⊓ centralizer ({w} : Set G)).subgroupOf (N ⊓ centralizer ({w} : Set G)) :=
    fun x hx => hK.le hx
  have hHsn : ((K.subgroupOf (N ⊓ centralizer ({w} : Set G))).subgroupOf
      ((A ⊓ centralizer ({w} : Set G)).subgroupOf
        (N ⊓ centralizer ({w} : Set G)))).IsSubnormal := by
    have h := hK.2.2.comap
      ((A ⊓ centralizer ({w} : Set G)).subgroupOfEquivOfLe hAB).toMonoidHom
    convert h using 1
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rfl
  have hAsn : ((A ⊓ centralizer ({w} : Set G)).subgroupOf
      (N ⊓ centralizer ({w} : Set G))).IsSubnormal := by
    have h := hsub.comap (Subgroup.inclusion (inf_le_left : N ⊓ centralizer ({w} : Set G) ≤ N))
    convert h using 1
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (Subgroup.mem_inf.mp x.2).2⟩⟩
  exact Subgroup.IsSubnormal.trans hKle hHsn hAsn

end CFSG.OddStandard.SmallF3.Omega
