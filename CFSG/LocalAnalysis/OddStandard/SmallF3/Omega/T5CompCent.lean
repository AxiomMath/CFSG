module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem t5_comp_not_central {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsOm6Z2 L)
    {s : G} (hs : s ∈ centralizer (L : Set G)) {J : Subgroup G}
    (hJ : IsComponentIn J (L ⊓ centralizer ({s} : Set G))) (h29 : IsL29 J) : False := by
  have hLcent : L ≤ centralizer ({s} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hs) x hx
  have hinf : L ⊓ centralizer ({s} : Set G) = L := inf_eq_left.mpr hLcent
  obtain ⟨hJLe, hK⟩ := hJ
  rw [hinf] at hK
  have hJL : J ≤ L := hJLe.trans inf_le_left
  have hTop : IsComponent (⊤ : Subgroup ↥L) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hL.1,
      Subgroup.IsSubnormal.top⟩
  rcases CFSG.LocalCores.distinct_components_commute hK hTop with hKtop | hKcomm
  ·
    have hLJ : L ≤ J := Subgroup.subgroupOf_eq_top.mp hKtop
    have hEq : J = L := le_antisymm hJL hLJ
    have h29' : LieModel (↥L ⧸ oddCore ↥L) .PSL 2 3 2 := hEq ▸ h29
    obtain ⟨hsimple, a, b, hab⟩ := ff_simple_of_lieModel_psl2 h29'
    have hcenter : Subgroup.center (↥L ⧸ oddCore ↥L) = ⊥ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ oddCore ↥L)) with h | h
      · exact h
      · exfalso
        haveI : IsMulCommutative (↥L ⧸ oddCore ↥L) := Subgroup.center_eq_top_iff.mp h
        exact hab (mul_comm' a b)
    have hcard : Nat.card (Subgroup.center (↥L ⧸ oddCore ↥L)) = 1 := by
      rw [hcenter, Subgroup.card_bot]
    have h2 : Nat.card (Subgroup.center (↥L ⧸ oddCore ↥L)) = 2 := hL.2.1
    omega
  ·
    have hKle : J.subgroupOf L ≤ Subgroup.center ↥L :=
      Subgroup.commutator_top_right_eq_bot_iff_le_center.mp hKcomm
    have hcomm : ⁅J.subgroupOf L, J.subgroupOf L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hKle.trans (Subgroup.center_le_centralizer (J.subgroupOf L : Set ↥L))
    haveI : IsMulCommutative ↥(J.subgroupOf L) :=
      Subgroup.commutator_self_eq_bot_iff.mp hcomm
    haveI : Nontrivial ↥(J.subgroupOf L) := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    haveI : Group.IsPerfect ↥(J.subgroupOf L) := hK.1.1
    exact Group.IsPerfect.not_isSolvable ↥(J.subgroupOf L) inferInstance


end CFSG.OddStandard.SmallF3.Omega
