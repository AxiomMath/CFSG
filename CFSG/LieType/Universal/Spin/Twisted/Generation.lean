module

public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Universal.Spin.Generation.Frame
public import CFSG.LieType.Universal.SpinClause0

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.ClassicalGroups.Orthogonal

variable (n : ℕ) {K : Type*} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem spinAction_twShortRoot_eq_eichler (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) (twShortRoot n hirr i s (.ofAdd p)) =
      eichler (quadMinus n K b c) (minusVec n i s) (planeVec n p) := by
  refine LinearEquiv.ext fun v => ?_
  rw [spinAction_twShortRoot, eichler_apply (quadMinus_minusVec n b c i s)
    (polar_minusVec_planeVec n b c i s p), quadMinus_planeVec', add_smul, sub_sub]

theorem minusDatum_iSup_eq_top {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) :
    ⨆ γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅, minusRootGroup n hirr γ = ⊤ := by
  have := isPerfect_spinGroup_quadMinus hn hirr
  refine (minusFrame n b c).toHypFrame.eq_top_of_longRoot_mem ?_ ?_ ?_
    (range_spinAction_quadMinus hn hirr).le
  · intro i j hij s t x
    have hγ := mem_roots_of_toStdB_eq_long n hij s t
      (toStdB_ofStdB (n - 1) (Pi.single i (boolSign s) + Pi.single j (boolSign t)))
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hγ
      (longRoot_mem_minusRootGroup n hirr hij s t (toStdB_ofStdB (n - 1) _) x))
  · intro i s v hv
    rw [eq_planeVec_of_polar_minusVec n b c hv, minusFrame_vec,
      ← spinAction_twShortRoot_eq_eichler n hirr i s]
    have hγ := mem_roots_of_toStdB_eq_short n i s
      (toStdB_ofStdB (n - 1) (Pi.single i (boolSign s)))
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hγ
      (twShortRoot_mem_minusRootGroup n hirr i s (toStdB_ofStdB (n - 1) _) _)))
  · intro v hv hQ
    rw [eq_planeVec_of_polar_minusVec n b c hv] at hQ ⊢
    rw [quadMinus_planeVec'] at hQ
    by_contra h0
    refine planeNorm_ne_zero hirr (fun hw => h0 ?_) hQ
    rw [hw, planeVec_zero]

end CFSG.LieType.Universal.Spin.Twisted
