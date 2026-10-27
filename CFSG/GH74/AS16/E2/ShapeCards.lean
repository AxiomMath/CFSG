module

public import CFSG.GH74.Orders.Sporadic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

theorem card_of_shapeL28 {K : Type} [Group K] (h : ShapeL28 K) : Nat.card K = 504 := by
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]
  decide

theorem card_of_shapeL33 {K : Type} [Group K] (h : ShapeL33 K) : Nat.card K = 5616 := by
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]
  decide

theorem card_of_shapeU33 {K : Type} [Group K] (h : ShapeU33 K) : Nat.card K = 6048 := by
  rw [CFSG.GH74.card_of_lieModel_PSU (by norm_num) (by norm_num) h]
  decide

theorem card_of_shapeSz8
    {K : Type} [Group K] (h : ShapeSz8 K) : Nat.card K = 29120 := by
  rw [CFSG.GH74.card_of_lieModel_twistedB2 h]
  decide

theorem card_of_shapeM11
    {K : Type} [Group K] (h : ShapeM11 K) : Nat.card K = 7920 :=
  CFSG.GH74.card_eq_of_isSporadic (s := .M11) CFSG.Semidihedral.GL2Recognition.card_nativeM11 h

theorem card_of_shape2M12
    {K : Type} [Group K] (h : Shape2M12 K) : Nat.card K = 190080 := by
  obtain ⟨-, hz, hq⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [hz, CFSG.GH74.card_of_isSporadic_M12 hq] at h1
  omega

theorem card_of_shape2Sz8
    {K : Type} [Group K] (h : Shape2Sz8 K) : Nat.card K = 58240 := by
  obtain ⟨-, hz, hq⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [hz, CFSG.GH74.card_of_lieModel_twistedB2 hq] at h1
  have h2 : CFSG.Open.ordSuzuki 8 = 29120 := by decide
  omega

end CFSG.GH74.AS16.E2
