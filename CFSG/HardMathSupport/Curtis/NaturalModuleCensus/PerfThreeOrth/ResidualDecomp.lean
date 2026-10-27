module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.Orthogonal.Basic
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

omit [CharP K 2] in
theorem res_x_cube (hx : OddOrderIsometry Q 3 x) (v : V) : x (x (x v)) = v := by
  have := congrArg (fun y : V ≃ₗ[K] V => y v) hx.pow_eq_one
  simpa [pow_succ] using this

omit [CharP K 2] in
theorem res_polar_x (hx : OddOrderIsometry Q 3 x) (v u : V) :
    polar Q (x v) (x u) = polar Q v u :=
  CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hx.mem v u

omit [CharP K 2] in
theorem res_map_x (hx : OddOrderIsometry Q 3 x) (v : V) : Q (x v) = Q v :=
  CFSG.ClassicalGroups.Orthogonal.map_of_mem hx.mem v

theorem res_projV1 (hx : OddOrderIsometry Q 3 x) (v : V) :
    x (v + x v + x (x v)) = v + x v + x (x v) ∧
      ∀ w, x w = w → polar Q w (v + x v + x (x v)) = polar Q w v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, fun w hw => ?_⟩
  · simp only [map_add, res_x_cube hx]
    abel
  · have h1 : polar Q w (x v) = polar Q w v := by
      have := res_polar_x hx w v
      rwa [hw] at this
    have h1' : polar Q w (x (x v)) = polar Q w v := by
      have := res_polar_x hx w (x v)
      rwa [hw, h1] at this
    rw [polar_add_right, polar_add_right, h1, h1']
    linear_combination (polar Q w v) * h2

theorem res_projV2 (hx : OddOrderIsometry Q 3 x) (v : V) :
    x (x (x v + x (x v))) + x (x v + x (x v)) + (x v + x (x v)) = 0 ∧
      ∀ w, x (x w) + x w + w = 0 → polar Q w (x v + x (x v)) = polar Q w v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, fun w hw => ?_⟩
  · simp only [map_add, res_x_cube hx]
    have e : ∀ a b c : V, a + b + (c + a) + (b + c) = (2 : K) • (a + b + c) := fun a b c => by
      module
    rw [e, h2, zero_smul]
  · have hc1 := (res_projV1 hx v).1
    have h1 : polar Q (x w) (v + x v + x (x v)) = polar Q w (v + x v + x (x v)) := by
      have := res_polar_x hx w (v + x v + x (x v))
      rwa [hc1] at this
    have h1' : polar Q (x (x w)) (v + x v + x (x v)) = polar Q w (v + x v + x (x v)) := by
      have := res_polar_x hx (x w) (v + x v + x (x v))
      rwa [hc1, h1] at this
    have h3 := congrArg (fun y => polar Q y (v + x v + x (x v))) hw
    simp only [polar_add_left, polar_zero_left, h1, h1'] at h3
    have h0 : polar Q w (v + x v + x (x v)) = 0 := by
      linear_combination h3 - (polar Q w (v + x v + x (x v))) * h2
    rw [add_assoc, polar_add_right] at h0
    linear_combination h0 - (polar Q w v) * h2

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
