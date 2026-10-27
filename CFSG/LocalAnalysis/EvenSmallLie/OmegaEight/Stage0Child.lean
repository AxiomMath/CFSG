module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Main

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage0

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

@[expose] def Hyp7 (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop :=
  StandardSetting G L ∧ center L = ⊥ ∧ CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1

@[expose] def EndgameA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G), Hyp7 G L → StepK t L →
    ShapeA t L → False

@[expose] def EndgameB7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t r : G), Hyp7 G L → StepK t L →
    ShapeB t L r → False

@[expose] def EndgameC'7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t c : G), Hyp7 G L → StepK t L →
    ShapeC' t L c → False

@[expose] def EndgameD'7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t c r : G), Hyp7 G L → StepK t L →
    ShapeD' t L c r → False

@[expose] def EndgameC7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t b : G), Hyp7 G L → StepK t L →
    ShapeC t L b → False

@[expose] def EndgameD7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t b r : G), Hyp7 G L → StepK t L →
    ShapeD t L b r → False

theorem childO8PlusCenterless_of_shapes (ha : EndgameA7)
    (hb : EndgameB7) (hc' : EndgameC'7) (hd' : EndgameD'7) (hc : EndgameC7) (hd : EndgameD7) :
    ChildO8PlusCenterless := by
  intro G _ _ L hset hZ h
  have hH : Hyp7 G L := ⟨hset, hZ, h⟩
  obtain ⟨-, t, hK, hA | ⟨r, hB⟩ | ⟨b, hC⟩ | ⟨b, r, hD⟩ | ⟨c, hC'⟩ | ⟨c, r, hD'⟩⟩ :=
    exists_shape_plus hset hZ h
  · exact ha G L t hH hK hA
  · exact hb G L t r hH hK hB
  · exact hc G L t b hH hK hC
  · exact hd G L t b r hH hK hD
  · exact hc' G L t c hH hK hC'
  · exact hd' G L t c r hH hK hD'

@[expose] def Hyp9 (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop :=
  StandardSetting G L ∧ center L = ⊥ ∧ CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1

@[expose] def EndgameA9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G), Hyp9 G L → StepK t L →
    ShapeA t L → False

@[expose] def EndgameC'9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t c : G), Hyp9 G L → StepK t L →
    ShapeC' t L c → False

@[expose] def EndgameC9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t b : G), Hyp9 G L → StepK t L →
    ShapeC t L b → False

theorem childO8Minus_of_shapes (ha : EndgameA9)
    (hc' : EndgameC'9) (hc : EndgameC9) : ChildO8Minus := by
  intro G _ _ L hset hZ h
  have hH : Hyp9 G L := ⟨hset, hZ, h⟩
  obtain ⟨-, t, hK, hA | ⟨b, hC⟩ | ⟨c, hC'⟩⟩ := exists_shape_minus hset hZ h
  · exact ha G L t hH hK hA
  · exact hc G L t b hH hK hC
  · exact hc' G L t c hH hK hC'

end CFSG.EvenSmallLie.OmegaEight.Stage0
