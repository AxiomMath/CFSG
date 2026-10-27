module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.CGT.PushingUpLit.CGT6

@[expose] def imSubOne {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.range (Matrix.mulVecLin ((g : Matrix (Fin n) (Fin n) (ZMod 2)) - 1))

@[expose] def routeCGroup {n : ℕ} (y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :=
  Subgroup.closure {y, d, t}

structure RouteCHyp {n : ℕ} (y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : Prop where
  y3 : y ^ 3 = 1
  d3 : d ^ 3 = 1
  rk_y : Module.finrank (ZMod 2) ↥(imSubOne y) = 2
  rk_d : Module.finrank (ZMod 2) ↥(imSubOne d) = 2
  t2 : t ^ 2 = 1
  t1 : t ≠ 1
  ty : t * y = y * t
  comm : imSubOne y ⊔ imSubOne d ⊔ imSubOne t = ⊤
  o2 : CFSG.pCore 2 ↥(routeCGroup y d t) = ⊥
  cent : ∀ s ∈ routeCGroup y d t, s ≠ 1 → s ^ 2 = 1 → s * y = y * s →
    ((Subgroup.zpowers y).subgroupOf
      (routeCGroup y d t ⊓ Subgroup.centralizer ({s} : Set _))).IsSubnormal

abbrev RouteCTriple (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) (ZMod 2) × Matrix (Fin n) (Fin n) (ZMod 2) ×
    Matrix (Fin n) (Fin n) (ZMod 2)

@[expose] def FinC (n : ℕ) (S : List (RouteCTriple n)) : Prop :=
  ∀ y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2), RouteCHyp y d t →
    ∃ g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2),
      (((g * y * g⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)),
        ((g * d * g⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)),
        ((g * t * g⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2))) ∈ S

end CFSG.CGT.PushingUpLit.CGT6
