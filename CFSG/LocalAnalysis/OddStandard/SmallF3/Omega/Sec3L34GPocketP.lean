module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L311Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_sl23PocketIn_of_data {x y : G} {X K : Subgroup G} (hD : Sec3PocketData x X y K) :
    Sl23PocketIn X y K := by
  obtain ⟨hyK, hKle, hKsub, hKSL⟩ := hD.pocket
  refine ⟨hyK, le_inf hD.le (hKle.trans inf_le_right), ?_, hKSL⟩
  exact isSubnormal_subgroupOf_of_le (inf_le_inf_right _ hD.component.1) hKsub

theorem l34g_normalizes_of_data [Finite G] {x y : G} {X K : Subgroup G}
    (hD : Sec3PocketData x X y K) {v : G} (hvx : v * x = x * v) (hvy : v * y = y * v) :
    v ∈ normalizer (X : Set G) := by
  have hnc := exists_noncomm_of_sl23PocketIn (inFStar_isQuasisimple hD.inFStar)
    (l34g_sl23PocketIn_of_data hD)
  refine sec63P_conjugate_eq_iff.mp
    (conjugate_eq_of_noncomm hD.component hD.mem hnc v ⟨?_, ?_⟩)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hvx
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hvy

theorem l34g_pocketData_of_pocketIn [Finite G] {v : G} {D : Subgroup G} (hv : orderOf v = 2)
    (hD : IsComponentIn D (centralizer ({v} : Set G))) (hDF : InFStar D) {b : G}
    {B : Subgroup G} (hb : orderOf b = 2) (hB : Sl23PocketIn D b B) :
    Sec3PocketData v D b B :=
  have hbD : b ∈ D := (hB.2.1 hB.1).1
  have hnc := exists_noncomm_of_sl23PocketIn (inFStar_isQuasisimple hDF) hB
  { involution_x := hv
    component := hD
    inFStar := hDF
    involution_y := hb
    mem := hbD
    le := hB.2.1.trans inf_le_left
    pocket := Sl23PocketIn.of_normal_centralizer hB hD.1 (conjugate_eq_of_noncomm hD hbD hnc) }

end CFSG.OddStandard.SmallF3.Omega
