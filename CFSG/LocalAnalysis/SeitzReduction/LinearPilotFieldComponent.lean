module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFieldComponentBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)

section Setting

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] [Finite K]

@[expose] noncomputable def fieldComponent (hn : 3 ≤ n) (e : L ≃* projectiveSL n K) :
    normalizer (L : Set G) →* (K ≃+* K) :=
  (linearFieldPart K hn).comp (normalizerAut e)

theorem fieldComponent_apply (hn : 3 ≤ n) (e : L ≃* projectiveSL n K)
    (x : normalizer (L : Set G)) :
    fieldComponent hn e x = linearFieldPart K hn (normalizerAut e x) :=
  rfl

theorem fieldComponent_eq_one_of_mem_centralizer (hn : 3 ≤ n) (e : L ≃* projectiveSL n K) {x : G}
    (hx : x ∈ centralizer (L : Set G)) :
    fieldComponent hn e ⟨x, centralizer_le_normalizer L hx⟩ = 1 := by
  rw [fieldComponent_apply, normalizerAut_eq_one_of_mem_centralizer e hx, map_one]

theorem fieldComponent_conj (hn : 3 ≤ n) (e : L ≃* projectiveSL n K)
    (x y : normalizer (L : Set G)) :
    fieldComponent hn e (y * x * y⁻¹) = fieldComponent hn e x := by
  rw [map_mul, map_mul, map_inv, ringEquiv_mul_comm (fieldComponent hn e y), mul_assoc,
    mul_inv_cancel, mul_one]

end Setting

end CFSG.SeitzReduction.LinearPilot
