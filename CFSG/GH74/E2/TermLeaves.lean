module

public import CFSG.GH74.E2.Terminal

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem two_le_pRank_of_commuting_involutions {H : Type*} [Group H] [Finite H] {a b : H}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hne : a ≠ b) (hab : a * b = b * a) :
    2 ≤ CFSG.pRank 2 H := by
  have ha2 : a * a = 1 := by rw [← sq]; exact sq_eq_one_of_orderOf ha
  have hb2 : b * b = 1 := by rw [← sq]; exact sq_eq_one_of_orderOf hb
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    omega
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb
    omega
  unfold CFSG.pRank
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨FourGroup.kleinFourOf a b ha2 hb2 hab,
    FourGroup.isElementaryAbelian_kleinFourOf, ?_⟩
  · rintro r ⟨B, -, hB⟩
    calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card H := Subgroup.card_le_card_group B
  · rw [FourGroup.card_kleinFourOf ha1 hb1 hne]
    norm_num

theorem noCaseIIAlphaA6_of (hComp : ComponentList) (hP : PumpUpData) : NoCaseIIAlphaA6 := by
  intro G _ _ hH t t' a A B K hc hK hsh _ _ ht'K
  obtain ⟨-, -, hrank⟩ := a6_terminal_facts hComp hP hH hc.order_t hK hsh
  have htC : t ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => (mem_Cen.1 (hK.1 hk)).symm
  have ht'C : t' ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => (ht'K k hk).symm
  have hrank2 : 2 ≤ CFSG.pRank 2 ↥(Subgroup.centralizer (K : Set G)) :=
    two_le_pRank_of_commuting_involutions (a := (⟨t, htC⟩ : ↥(Subgroup.centralizer (K : Set G))))
      (b := ⟨t', ht'C⟩) (by rw [← Subgroup.orderOf_coe]; exact hc.order_t)
      (by rw [← Subgroup.orderOf_coe]; exact hc.order_t')
      (fun h => hc.ne (congrArg (fun x : ↥(Subgroup.centralizer (K : Set G)) => (x : G)) h))
      (Subtype.ext hc.comm)
  omega

end CFSG.GH74.E2
