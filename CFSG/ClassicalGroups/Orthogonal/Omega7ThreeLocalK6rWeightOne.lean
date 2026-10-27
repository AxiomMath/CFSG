module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRootOrder

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open

variable {K : Type} [Field K]

theorem exists_commuting_pair_weight_one [Finite K] (F : Frame K) :
    ∃ x y : ↥(Omega7 K),
      x ∈ Subgroup.centralizer ({c₀ F (Multiplicative.ofAdd ![1, 0, 0])} : Set ↥(Omega7 K)) ∧
      y ∈ Subgroup.centralizer ({c₀ F (Multiplicative.ofAdd ![1, 0, 0])} : Set ↥(Omega7 K)) ∧
      orderOf x = ringChar K ∧ orderOf y = ringChar K ∧ Commute x y ∧
      y ∉ Subgroup.zpowers x := by
  obtain ⟨s, t, hst⟩ := exists_planeNorm_eq F.hK F.h3 (-1)
  have hQu : modelQuad K F.a (vecOf K ![0, 1, s] ![0, 0, t] 0) = 0 := by
    rw [modelQuad_vecOf]
    simp
    linear_combination hst
  have hu0 : vecOf K ![0, 1, s] ![0, 0, t] 0 ≠ 0 := by
    intro h
    have := congrFun h (.inl 1)
    simp at this
  have hBu' : modelPolar K F.a (vecOf K ![0, 1, s] ![0, 0, t] 0)
      (vecOf K ![0, 0, -t] ![0, 1, s - t] 0) = 0 := by
    rw [modelPolar_vecOf]
    simp
    linear_combination (-1 : K) * hst
  have hBz : modelPolar K F.a (vecOf K ![0, 1, s] ![0, 0, t] 0) (vecOf K 0 0 1) = 0 := by
    rw [modelPolar_vecOf]
    simp
  have hu'ne : ∀ c : K,
      vecOf K ![0, 0, -t] ![0, 1, s - t] 0 ≠ c • vecOf K ![0, 1, s] ![0, 0, t] 0 := by
    intro c h
    have := congrFun h (.inr (.inl 1))
    simp at this
  have hzne : ∀ c : K, vecOf K 0 0 1 ≠ c • vecOf K ![0, 1, s] ![0, 0, t] 0 := by
    intro c h
    have := congrFun h (.inr (.inr ()))
    simp at this
  have hfix : ∀ {xs ys : Fin 3 → K} {z : K}, xs 0 = 0 → ys 0 = 0 →
      rotMat K ![1, 0, 0] *ᵥ vecOf K xs ys z = vecOf K xs ys z := by
    intro xs ys z h0 h0'
    rw [rotMat_mulVec_vecOf, vecOf_eq_iff]
    refine ⟨funext fun i => ?_, funext fun i => ?_, rfl⟩ <;> fin_cases i <;>
      simp [planeRot_one, planeRot_zero, h0, h0']
  have hcu := commute_c₀_omegaRoot F (Multiplicative.ofAdd ![1, 0, 0])
    (hfix (xs := ![0, 1, s]) (ys := ![0, 0, t]) (z := 0) rfl rfl)
    (hfix (xs := ![0, 0, -t]) (ys := ![0, 1, s - t]) (z := 0) rfl rfl)
  have hcz := commute_c₀_omegaRoot F (Multiplicative.ofAdd ![1, 0, 0])
    (hfix (xs := ![0, 1, s]) (ys := ![0, 0, t]) (z := 0) rfl rfl)
    (hfix (xs := 0) (ys := 0) (z := 1) rfl rfl)
  have hx1 := omegaRoot_ne_one_of_not_mem_span F hQu hu0 hBu' hu'ne
  have hy1 := omegaRoot_ne_one_of_not_mem_span F hQu hu0 hBz hzne
  refine ⟨omegaRoot F _ _, omegaRoot F _ _, ?_, ?_, orderOf_omegaRoot F hx1,
    orderOf_omegaRoot F hy1, commute_omegaRoot_same_center F hBu' hBz, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hcu.symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hcz.symm
  · refine omegaRoot_not_mem_zpowers F hQu hu0 hBu' hBz fun k c h => ?_
    have := congrFun h (.inr (.inr ()))
    simp at this

theorem two_le_pRank_centralizer_c₀_weight_one [Finite K] (F : Frame K) :
    2 ≤ pRank (ringChar K)
      (Subgroup.centralizer ({c₀ F (Multiplicative.ofAdd ![1, 0, 0])} : Set ↥(Omega7 K))) := by
  obtain ⟨x, y, hx, hy, hxo, hyo, hxy, hyx⟩ := exists_commuting_pair_weight_one F
  exact two_le_pRank_ringChar_of_commute hx hy hxo hyo hxy hyx

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
