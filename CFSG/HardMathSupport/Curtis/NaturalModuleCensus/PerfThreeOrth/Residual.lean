module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.ResidualStepA
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.ResidualFixed

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem exists_twoPower_centralizer_moving (hK : Nat.card K = 2)
    (hx : OddOrderIsometry Q 3 x) (hdim : Module.finrank K V = 8)
    (hmax : ∃ U : Submodule K V, Module.finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0)
    (hfix : Module.finrank K (fixedSpace x) = 4 ∨ Module.finrank K (fixedSpace x) = 2)
    (W : Submodule K V) (hW0 : W ≠ ⊥) (hWts : ∀ w ∈ W, Q w = 0) (hWx : ∀ w ∈ W, x w ∈ W) :
    ∃ g : V ≃ₗ[K] V, g ∈ isometryCentralizer Q x ∧
      g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      (∃ k : ℕ, g ^ (2 ^ k) = 1) ∧ ∃ w ∈ W, g w ∉ W := by
  by_cases hV2 : ∃ w ∈ W, w ≠ 0 ∧ x (x w) + x w + w = 0
  · obtain ⟨w, hwW, hw0, hw2⟩ := hV2
    exact res_exists_move_of_mem_V2 hK hx (res_exists_three_of_four hmax) hWts hWx hwW hw0 hw2
  · push Not at hV2
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hy : x w + x (x w) = 0 := by
      by_contra hy
      exact hV2 _ (W.add_mem (hWx w hwW) (hWx _ (hWx w hwW))) hy (res_projV2 hx w).1
    have hwx : x w = w := by
      have e1 : x w = x (x w) := by
        have := eq_neg_of_add_eq_zero_left hy
        rwa [neg_eq_of_add_eq_zero_right (res_add_self K (x (x w)))] at this
      have e2 : x (x w) = w := by
        have := congrArg x e1
        rw [res_x_cube hx] at this
        exact this
      rw [e1, e2]
    exact res_exists_move_of_fixed hK hx hdim hmax hfix hWts hwW hw0 hwx

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
