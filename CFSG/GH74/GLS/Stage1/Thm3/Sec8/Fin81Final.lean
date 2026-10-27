module

public import CFSG.Blueprint.ChevalleyBinomial
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Core
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Dih
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 Fin81

theorem central_eq_of_equiv_M128 {H : Type*} [Group H] (g : M128 ≃* H) {z : H} (hz1 : z ≠ 1)
    (hzc : ∀ s, s * z = z * s) : ∀ y : H, (∀ s, s * y = y * s) → y = 1 ∨ y = z := by
  have hz : g.symm z = zeta := by
    have hc1 : ∀ y : M128, g.symm z * y = y * g.symm z := fun y => by
      have := hzc (g y)
      apply g.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact this.symm
    rcases center_M128 _ hc1 with h1 | h1
    · exact absurd (g.symm.injective (by rw [h1, map_one])) hz1
    · exact h1
  intro y hy
  have hc1 : ∀ w : M128, g.symm y * w = w * g.symm y := fun w => by
    have := hy (g w)
    apply g.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact this.symm
  rcases center_M128 _ hc1 with h1 | h1
  · left; exact g.symm.injective (by rw [h1, map_one])
  · right; exact g.symm.injective (by rw [h1, hz])

theorem central_mem_sylow {X : Type*} [Group X] (P : Sylow 2 X) {c : X} (hc : c ∈ Subgroup.center X)
    (ho : orderOf c = 2) : c ∈ (P : Subgroup X) := by
  have hN : (Subgroup.zpowers c).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcomm : Commute g c := Subgroup.mem_center_iff.1 hc g
    rw [(hcomm.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  have hP : IsPGroup 2 ↥(Subgroup.zpowers c) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ho]; norm_num
  exact hP.le_sylow_of_normal P (Subgroup.mem_zpowers c)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
