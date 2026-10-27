module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L182
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L182O2Kind

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

theorem L182O2.z_mem_Op2 {G : Type} [Group G] [Finite G] {z : G} (hz2 : orderOf z = 2) :
    z ∈ Op 2 (Cen z) := by
  have hW : IsPGroup 2 ↥(zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hle : zpowers z ≤ Op 2 (Cen z) :=
    CFSG.GH74.GLS.Stage2.Final.Thm6.L20.le_Op_of_normalized 2
      (Subgroup.zpowers_le.2 (mem_Cen_self z)) (fun b hb w hw => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        have hbz : Commute b z := Subgroup.mem_centralizer_singleton_iff.1 hb
        have : b * z ^ m * b⁻¹ = z ^ m := by
          rw [(hbz.zpow_right m).eq]
          group
        rw [this]
        exact Subgroup.zpow_mem_zpowers z m) hW
  exact hle (Subgroup.mem_zpowers z)

theorem L182O2.one_le_pRank_Op2 {G : Type} [Group G] [Finite G] {z : G} (hz2 : orderOf z = 2) :
    1 ≤ pRank 2 ↥(Op 2 (Cen z)) := by
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  exact L182.one_le_pRank_of_involution (Q := ↥(Op 2 (Cen z))) (a := ⟨z, L182O2.z_mem_Op2 hz2⟩)
    (Subtype.ext hzz) (fun h => hz1 (congrArg Subtype.val h))

theorem o2RankOne_thm : O2RankOne := by
  intro G _ _ z k S ctx hns
  obtain ⟨A, hTA, hA⟩ := L182O2.exists_unique_inv ctx hns
  exact le_antisymm (L182O2.pRank_Op2_le_one hTA hA) (L182O2.one_le_pRank_Op2 ctx.orderOf_z)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
