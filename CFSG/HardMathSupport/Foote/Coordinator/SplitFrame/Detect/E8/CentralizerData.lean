module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.RootData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

@[expose] def leviWord5 : List (Fin Tag.E8.rank) :=
  [6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7]

@[expose] def leviWord6 : List (Fin Tag.E8.rank) :=
  [7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7]

@[expose] def leviWord7 : List (Fin Tag.E8.rank) :=
  [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7]

theorem leviWord_theta :
    leviWord5.foldr (reflect .E8) theta = Pi.single 5 1 ∧
    leviWord6.foldr (reflect .E8) theta = Pi.single 6 1 ∧
    leviWord7.foldr (reflect .E8) theta = Pi.single 7 1 := by decide +kernel

theorem leviWord_min : ∀ β ∈ rootFinset .E8, β 7 = 0 → 0 < height β →
    0 < height (leviWord5.foldr (reflect .E8) β) ∧ 0 < height (leviWord6.foldr (reflect .E8) β) ∧
      0 < height (leviWord7.foldr (reflect .E8) β) := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem perp_inter_E8 : ∀ β ∈ rootFinset .E8, β 7 = 0 → 0 < height β →
    iform β (Pi.single 5 1) = 0 → iform β (Pi.single 6 1) = 0 → iform β (Pi.single 7 1) = 0 →
    β ∈ e8ListA := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem single_mem_S2set : ∀ j : Fin Tag.E8.rank, j.val < 4 →
    (Pi.single j 1 : Fin Tag.E8.rank → ℤ) ∈ e8ListA ∧
      (-Pi.single j 1 : Fin Tag.E8.rank → ℤ) ∈ e8ListA := by decide +kernel

theorem single_mem_S1set' : ∀ j : Fin Tag.E8.rank, j.val = 5 ∨ j.val = 6 ∨ j.val = 7 →
    (Pi.single j 1 : Fin Tag.E8.rank → ℤ) ∈ e8ListB ∧
      (-Pi.single j 1 : Fin Tag.E8.rank → ℤ) ∈ e8ListB := by decide +kernel

@[expose] def w5 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd leviWord5

@[expose] def w6 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd leviWord6

@[expose] def w7 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd leviWord7

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
