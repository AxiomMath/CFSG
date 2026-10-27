module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTransLayerAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem t5_oddCore_layer_le_center {H : Type} [Group H] [Finite H] :
    CFSG.oddCore ↥(CFSG.layer H) ≤ Subgroup.center ↥(CFSG.layer H) := by
  let E := CFSG.layer H
  let R : Subgroup H := (CFSG.oddCore ↥E).map E.subtype
  have hcard : Nat.card ↥R = Nat.card ↥(CFSG.oddCore ↥E) :=
    Subgroup.card_map_of_injective E.subtype_injective
  have hRsol : Group.IsSolvable ↥R := by
    refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
    rw [hcard]
    exact ff_odd_card_oddCore ↥E
  have hRE : R ≤ E := Subgroup.map_subtype_le (CFSG.oddCore ↥E)
  have hsub : R.IsSubnormal := by
    refine Subgroup.IsSubnormal.step R E hRE ?_ ?_
    · haveI : E.Characteristic := CFSG.LocalCores.layer_characteristic (G := H)
      exact (inferInstance : E.Normal).isSubnormal
    · have heq : R.subgroupOf E = CFSG.oddCore ↥E :=
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective (CFSG.oddCore ↥E)
      rw [heq]
      exact inferInstance
  have hcomm : ⁅R, E⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (CFSG.LocalCores.component_solvable_centralizer hRsol hsub).2
  have hle : R ≤ Subgroup.centralizer (E : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro x hx
  refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
  exact Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_map_of_mem E.subtype hx))
    (E.subtype y) y.2

theorem t5_isQuasisimple_layer_of_isL29 {H : Type} [Group H] [Finite H]
    (h : LieModel (↥(CFSG.layer H) ⧸ CFSG.oddCore ↥(CFSG.layer H)) .PSL 2 3 2) :
    CFSG.IsQuasisimple ↥(CFSG.layer H) := by
  obtain ⟨hsimple, hnc⟩ := ff_simple_of_lieModel_psl2 h
  haveI : IsSimpleGroup (↥(CFSG.layer H) ⧸ CFSG.oddCore ↥(CFSG.layer H)) := hsimple
  haveI : Group.IsPerfect ↥(CFSG.layer H) := CFSG.LocalCores.layer_isPerfect
  have hcenter : Subgroup.center ↥(CFSG.layer H) = CFSG.oddCore ↥(CFSG.layer H) := by
    refine le_antisymm ?_ t5_oddCore_layer_le_center
    intro z hz
    have hzX : (QuotientGroup.mk z : ↥(CFSG.layer H) ⧸ CFSG.oddCore ↥(CFSG.layer H)) ∈
        Subgroup.center (↥(CFSG.layer H) ⧸ CFSG.oddCore ↥(CFSG.layer H)) := by
      refine Subgroup.mem_center_iff.mpr fun q => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz y]
    have hQ : Subgroup.center (↥(CFSG.layer H) ⧸ CFSG.oddCore ↥(CFSG.layer H)) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (↥(CFSG.layer H) ⧸ CFSG.oddCore ↥(CFSG.layer H))) with h1 | h1
      · exact h1
      · exfalso
        haveI : IsMulCommutative (↥(CFSG.layer H) ⧸ CFSG.oddCore ↥(CFSG.layer H)) :=
          center_eq_top_iff.mp h1
        exact Group.IsPerfect.not_isMulCommutative
          (↥(CFSG.layer H) ⧸ CFSG.oddCore ↥(CFSG.layer H)) inferInstance
    rw [hQ, Subgroup.mem_bot] at hzX
    exact (QuotientGroup.eq_one_iff z).mp hzX
  let e : (↥(CFSG.layer H) ⧸ Subgroup.center ↥(CFSG.layer H)) ≃*
      (↥(CFSG.layer H) ⧸ CFSG.oddCore ↥(CFSG.layer H)) :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  refine ⟨CFSG.LocalCores.layer_isPerfect, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩

theorem t5_isComponentIn_layer_of_isL29 {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (h : IsL29 (CFSG.inSubgroup CFSG.layer H)) :
    IsComponentIn (CFSG.inSubgroup CFSG.layer H) H := by
  refine ⟨Subgroup.map_subtype_le (CFSG.layer ↥H), ?_⟩
  have hsub : (CFSG.inSubgroup CFSG.layer H).subgroupOf H = CFSG.layer ↥H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective (CFSG.layer ↥H)
  rw [hsub]
  refine ⟨?_, ?_⟩
  · refine t5_isQuasisimple_layer_of_isL29 (H := ↥H) ?_
    let e := (CFSG.layer ↥H).equivMapOfInjective H.subtype H.subtype_injective
    exact (ff_lieModel_quot_oddCore_iff e).mpr h
  · haveI : (CFSG.layer ↥H).Characteristic :=
      CFSG.LocalCores.layer_characteristic (G := ↥H)
    exact (inferInstance : (CFSG.layer ↥H).Normal).isSubnormal

end CFSG.OddStandard.SmallF3.Omega
