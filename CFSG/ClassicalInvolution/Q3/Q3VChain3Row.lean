module

public import CFSG.ClassicalInvolution.Q3.Q3VRow
public import CFSG.ClassicalInvolution.Q3.Q3VChain3Frame
public import CFSG.ClassicalInvolution.Q3.Q3VFrameMain
public import CFSG.ClassicalInvolution.Q3.Q3VLiftMain
public import CFSG.ClassicalInvolution.Q3.Q3WARow

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Chain3

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

@[expose] def LayersCommute4 {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Fin 4 → Subgroup G) :
    Prop :=
  Commutes (layerSub Ω K 0 1) (layerSub Ω K 2 3) ∧
    Commutes (layerSub Ω K 0 3) (layerSub Ω K 1 2)

@[expose] def Sp3F4NoncommInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), Q3W.RouteD3Setup K z →
      Q3W.LocalShapeC3 1 (CompData.model .PSp 3) (conjClass3 K) z →
      Q3W.LocalOddThreeFree3 (conjClass3 K) z →
      (∃ Kf : Fin 4 → Subgroup G, IsMemberFrame (conjClass3 K) Kf ∧
        ¬ LayersCommute4 (conjClass3 K) Kf) → Blueprint.OddLieType G

theorem piece3Sp3_of_noncomm (h3 : Q3W.OddThreeFreeInput) (hF4 : Sp3F4NoncommInput) :
    Q3W.Piece3Sp3 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  have hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z := h3 G K z hR
  obtain ⟨Θ₀, hΘ₀⟩ := Lift.exists_locLift (by norm_num) hR hshape hO3
  have hK₀ : ¬ Commutes K K := Q3W.not_commutes_self3 hR.cls
  obtain ⟨Kf, Θ, -, hK, hΘ⟩ := Frame.exists_frame_lifts (by norm_num) hK₀ hΘ₀
  by_cases hc : LayersCommute4 (conjClass3 K) Kf
  · exact Or.inl (oddLieType_of_local_four hnab hR hshape hO3 hK hΘ hc.1 hc.2)
  · exact Or.inl (hF4 G hnab K z hR hshape hO3 ⟨Kf, hK, hc⟩)

end CFSG.ClassicalInvolution.Q3.Q3V.Chain3
