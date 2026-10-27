module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

structure ConjTy (G : Type*) [Group G] where
  val : List G

instance conjMulAction {G : Type*} [Group G] (H : Subgroup G) : MulAction ↥H (ConjTy G) where
  smul h x := ⟨x.val.map fun y => (h : G) * y * (h : G)⁻¹⟩
  one_smul x := by
    show ConjTy.mk (x.val.map fun y => ((1 : ↥H) : G) * y * ((1 : ↥H) : G)⁻¹) = x
    cases x
    simp
  mul_smul h k x := by
    show ConjTy.mk (x.val.map fun y => ((h * k : ↥H) : G) * y * ((h * k : ↥H) : G)⁻¹) =
      ConjTy.mk ((x.val.map fun y => (k : G) * y * (k : G)⁻¹).map fun y => (h : G) * y * (h : G)⁻¹)
    simp [Function.comp_def, mul_assoc]

end CFSG.GF2Type.Smith1979.IdxFour
