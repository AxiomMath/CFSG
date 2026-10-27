module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Y14
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Assembly

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open Subgroup CFSG.Blueprint CFSG.Fischer

variable {G : Type} [Group G] {L : Subgroup G}

theorem y14Coords_sec3DData (e : L ≃* T46) (t : G) :
    Child5.Y14Coords (sec3DData e t) (theta2G e) (iotaY e) where
  K₂_eq := range_theta2G e
  ι_mem := iotaY_mem
  ι_add := iotaY_add
  ι_inj _ h := iotaY_eq_one h
  K₂_ι := theta2G_conj_iotaY
  E_mem _ hm := theta2G_gen3_mem_sA₁ hm
  ν_mem _ hj := theta2G_nu_mem_sK₁ hj

theorem y14CoordInput : Child5.Y14CoordInput := by
  intro G _ _ L _ _ _ t _ _ e
  exact ⟨theta2G e, iotaY e, y14Coords_sec3DData e t, fun _ hu => theta2G_mem_sS hu,
    theta2G_s01⟩

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
