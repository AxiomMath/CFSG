module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpMain

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem inf_centerIn_eq_bot_of_not_wCentralNontrivial {Y : Type} [Group Y] {W : Subgroup Y}
    (hnc : ¬ WCentralNontrivial W) :
    W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set Y)) = ⊥ := by
  have hZ : W ⊓ CFSG.centerIn (Subgroup.normalizer (W : Set Y)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxW, -, hxC⟩
    by_contra hx
    apply hnc
    refine ⟨x, hxW, fun h1 => hx (by rw [h1]; exact Subgroup.one_mem _), fun g hg => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hxC g hg)
  have e : CFSG.centerIn (Subgroup.normalizer (W : Set Y)) =
      Asc77.centerIn (Subgroup.normalizer (W : Set Y)) := CFSG.centerIn_eq_map_center _
  rwa [e] at hZ

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
