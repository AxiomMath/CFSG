module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Model
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusModel
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter

public section

namespace CFSG.GroupTheory.GomiLeviExc

open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LieType.Universal
  CFSG.LieType.Steinberg

theorem SpinPlusModel.isCharTwoSteinberg (K : Type) [Field K] [CharP K 2] {n : ℕ} (hn : 3 ≤ n) :
    IsCharTwoSteinberg (Spin.plusDatum n K hn).roots (SpinPlus.x n K hn) := by
  change IsCharTwoSteinberg (SpinPlus.Φ n K hn).roots (SpinPlus.x n K hn)
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (Spin.isFiniteType_cartanD n) (Dv := ∅) rfl
  refine ⟨fun γ hγ c d => (SpinPlus.isParametrization hn γ hγ).2.1 c d, ?_⟩
  intro α hα β hβ hαβ c d
  have hcomm := SpinPlus.commutatorFormula hn O α hα β hβ hαβ c d
  have hcoef : ((SpinPlus.commC α β (1, 1) : ℤ) : K) = 1 := by
    rcases Int.natAbs_eq_iff.mp (SpinPlus.commC_natAbs α β (1, 1)) with h | h
    · rw [h]
      norm_num
    · rw [h, Int.cast_neg, CharTwo.neg_eq]
      norm_num
  by_cases hr : α + β ∈ (SpinPlus.Φ n K hn).roots
  · rw [if_pos hr, hcomm, (SpinPlus.commOrder_list_eq hn O hα hβ hαβ).1 hr,
      List.map_singleton, List.prod_singleton, one_smul, one_smul, pow_one, pow_one]
    rw [hcoef, one_mul]
  · rw [if_neg hr, hcomm, (SpinPlus.commOrder_list_eq hn O hα hβ hαβ).2 hr,
      List.map_nil, List.prod_nil]

variable (K : Type) [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem isCharTwoModel_spinPlus (hn : 4 ≤ n) :
    IsCharTwoModel (Spin.plusDatum n K (Nat.le_of_succ_le hn)) K
      (SpinPlus.x n K (Nat.le_of_succ_le hn)) where
  conclusionB := SpinPlus.conclusionB (Nat.le_of_succ_le hn)
  divisible := rfl
  isSymm := by
    change (Spin.cartanD n).IsSymm
    rw [Spin.cartanD_eq]
    exact CartanMatrix.D_isSymm n
  steinberg := SpinPlusModel.isCharTwoSteinberg K (Nat.le_of_succ_le hn)
  isQuasisimple :=
    (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isChevComponent_spinPlus (F := K) hn).1
  odd_card_center := by
    rw [(CFSG.StandardType.OrthRest.spinPlus_bij (K := K) (by omega : 3 ≤ n)).2, Subgroup.card_bot]
    exact odd_one
  isChevTwo := isChevTwo_of_classicalTwoOrG2
    (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isChevComponent_spinPlus (F := K) hn).2

theorem hasCharTwoModel_D (hn : 4 ≤ n) : HasCharTwoModel K (CartanMatrix.D n) :=
  ⟨_, _, Spin.plusDatum n K (Nat.le_of_succ_le hn), SpinPlus.x n K (Nat.le_of_succ_le hn),
    Equiv.refl _, fun i j => by
      change Spin.cartanD n i j = _
      rw [Spin.cartanD_eq], isCharTwoModel_spinPlus K hn⟩

end CFSG.GroupTheory.GomiLeviExc
