module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZB1
import CFSG.ClassicalInvolution.Asc77.AscT8ZB2Eng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY

namespace T8ZZ


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem vGroup_le_layerJoin (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t) :
    F.vGroup ≤ T8.layerJoin Ω (z * t) := by
  unfold FrameData.vGroup
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact (T8.layerJoin Ω (z * t)).mul_mem (frame_zz_mem_layerJoin hs F 0)
      (frame_zz_mem_layerJoin hs F 1)
  · exact (T8.layerJoin Ω (z * t)).mul_mem (frame_zz_mem_layerJoin hs F 0)
      (frame_zz_mem_layerJoin hs F 2)

theorem layerCenter_of_central [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (F : FrameData Ω W K J z t)
    (h01 : T8V.layerMk (z * t) (F.zz 0) (frame_zz_mem_layerJoin hs F 0) *
      T8V.layerMk (z * t) (F.zz 1) (frame_zz_mem_layerJoin hs F 1) ∈
        Subgroup.center (T8.LayerQuot Ω (z * t)))
    (h02 : T8V.layerMk (z * t) (F.zz 0) (frame_zz_mem_layerJoin hs F 0) *
      T8V.layerMk (z * t) (F.zz 2) (frame_zz_mem_layerJoin hs F 2) ∈
        Subgroup.center (T8.LayerQuot Ω (z * t)))
    (hcard : Nat.card (Subgroup.center (T8.LayerQuot Ω (z * t))) ≤ 4) :
    F.vGroup ≤ zStarOf (T8.layerJoin Ω (z * t)) ∧
      zStarOf (T8.layerJoin Ω (z * t)) ≤
        F.vGroup ⊔ oddCoreOf (T8.layerJoin Ω (z * t)) := by
  exact layerCenter_of_centralE F (fun i => frame_zz_mem_layerJoin hs F i) F.vGroup rfl
    (alphaOf_vGroup_eq hs F).1 (vGroup_le_layerJoin hs F) h01 h02 hcard

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
