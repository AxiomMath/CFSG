module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Config

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

namespace CoreConfig

variable {Y : Subgroup X} {u z : X}

theorem mem_twoCore (hc : CoreConfig Y u z) : u ∈ CFSG.Open.pCore 2 X := by
  have hnorm : (Subgroup.zpowers u).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [((hc.commute_center g).zpow_right k).eq, mul_inv_cancel_right]
    exact hn
  exact le_twoCore hnorm (isPGroup_zpowers_of_orderOf_eq_two hc.order) (Subgroup.mem_zpowers u)

theorem twoCore_le (hc : CoreConfig Y u z) : CFSG.Open.pCore 2 X ≤ Y := by
  obtain ⟨P, hPY, -, -, -⟩ := hc.sylow
  exact ((twoCore_isPGroup X).le_sylow_of_normal P).trans hPY

theorem twoCore_pRank (hc : CoreConfig Y u z) :
    CFSG.Open.pRank 2 (CFSG.Open.pCore 2 X) = 1 := by
  have hle : CFSG.Open.pRank 2 (CFSG.Open.pCore 2 X) ≤ 1 := by
    by_contra h
    have hN := hc.normalizer_le _ hc.twoCore_le (by omega)
    rw [Subgroup.normalizer_eq_top] at hN
    exact hc.ne_top (top_le_iff.mp hN)
  have hu2 : u ^ 2 = 1 := by rw [← hc.order, pow_orderOf_eq_one]
  have helem : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers u) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self u i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2, one_zpow]
  have hge : 1 ≤ CFSG.Open.pRank 2 (CFSG.Open.pCore 2 X) :=
    CFSG.SectionRank.le_pRank (by decide) (Subgroup.zpowers_le.mpr hc.mem_twoCore) helem
      (by rw [Nat.card_zpowers, hc.order, pow_one])
  omega

end CoreConfig

end CFSG.ProperTwoGeneratedCore.TheoremC
