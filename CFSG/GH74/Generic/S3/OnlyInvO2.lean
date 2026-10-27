module

public import CFSG.GH74.Generic.S3.LeavesR
public import CFSG.GH74.Generic.S3.PumpLift
public import CFSG.GH74.Generic.S3.PumpDiag
public import CFSG.GH74.Generic.Lifting
public import CFSG.GH74.GLS.TwoThin.Pumpup
public import CFSG.GH74.GLS.TwoThin.PumpData
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.S3.J2Star
public import CFSG.GH74.Generic.JMaxDefs
public import CFSG.GH74.AS16.Standard
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.GH74.AS16.Defs

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.LocalAnalysis.ComponentInitial

theorem two_le_pRank_of_two_involutions {P : Type*} [Group P] [Finite P] {a b : P}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hne : a ≠ b) (hc : Commute a b) :
    2 ≤ CFSG.pRank 2 P := by
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; omega
  have hZa : IsElementaryAbelian 2 (zpowers a) := IsElementaryAbelian.zpowers_of_pow_eq_one ha2
  have hZb : IsElementaryAbelian 2 (zpowers b) := IsElementaryAbelian.zpowers_of_pow_eq_one hb2
  have hbc : zpowers b ≤ centralizer ((zpowers a : Subgroup P) : Set P) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (hc.zpow_left k).eq
  have hE : IsElementaryAbelian 2 ↥(zpowers a ⊔ zpowers b) :=
    have := hZa
    have := hZb
    IsElementaryAbelian.sup_of_le_centralizer hbc
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 ↥(zpowers a ⊔ zpowers b)).exists_card_eq
  have hle : zpowers a ≤ zpowers a ⊔ zpowers b := le_sup_left
  have hcard_a : Nat.card ↥(zpowers a) = 2 := by rw [Nat.card_zpowers, ha]
  have h2 : 2 ≤ Nat.card ↥(zpowers a ⊔ zpowers b) := by
    rw [← hcard_a]; exact Subgroup.card_le_of_le hle
  have hne2 : Nat.card ↥(zpowers a ⊔ zpowers b) ≠ 2 := by
    intro h
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard_a, h])
    have hbmem : b ∈ zpowers a ⊔ zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    rw [← heq] at hbmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbmem
    have : a ^ k = 1 ∨ a ^ k = a := by
      rcases Int.even_or_odd' k with ⟨l, rfl | rfl⟩
      · left; rw [zpow_mul]; simp [ha2]
      · right; rw [zpow_add, zpow_mul]; simp [ha2]
    rcases this with h1 | h1
    · exact hb1 (hk ▸ h1)
    · exact hne (hk ▸ h1).symm
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : m ≤ 1 := by omega
    have hle2 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    rw [hm] at h2 hne2
    omega
  exact hm2.trans (le_pRank_of_card' one_lt_two _ hE hm)

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}

end CFSG.GH74.Generic.S3
