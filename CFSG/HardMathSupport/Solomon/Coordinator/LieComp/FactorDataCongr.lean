module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem LieFactorData.of_mulEquiv {q : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : LieFactorData q X) : LieFactorData q Y := by
  have hZ : (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y := Subgroup.map_center_eq e
  let g : (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) := QuotientGroup.congr _ _ e hZ
  have hcard : Nat.card (Subgroup.center Y) = Nat.card (Subgroup.center X) := by
    rw [← hZ, Subgroup.card_map_of_injective e.injective]
  refine ⟨?_, isChevSimple_congr g h.chev, fun ⟨a⟩ h3 => h.centre ⟨g.trans a⟩ ?_⟩
  · have hmap := congrArg (Subgroup.map e.toMonoidHom) h.perfect
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective] at hmap
    rw [commutator_def]
    exact hmap
  · rwa [hcard] at h3

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

end
