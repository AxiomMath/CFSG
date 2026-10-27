module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem L3U3Pumpup.exists_order_dvd_lt {S : Type} [Group S] [Finite S] {β : MulAut S}
    (hF : L3U3Facts) (h : L3U3Pumpup S β) :
    ∃ N : ℕ, L3U3Order N ∧ N ∣ Nat.card S ∧ N < Nat.card S := by
  obtain ⟨-, hβ1, J, hJ, hL⟩ := h
  have hJle : J ≤ fixSubgroup β := hJ.1
  have hne : fixSubgroup β ≠ ⊤ := by
    intro htop
    refine hβ1 (MulEquiv.ext fun s => ?_)
    have hs : s ∈ fixSubgroup β := htop ▸ Subgroup.mem_top s
    exact mem_fixSubgroup.1 hs
  have hquot : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  refine ⟨Nat.card (PQuot 3 J), hF.order _ hL, hquot.trans (Subgroup.card_subgroup_dvd_card J), ?_⟩
  calc Nat.card (PQuot 3 J) ≤ Nat.card J := Nat.le_of_dvd Nat.card_pos hquot
    _ ≤ Nat.card (fixSubgroup β) := Subgroup.card_le_of_le hJle
    _ < Nat.card S := (Subgroup.card_le_card_group _).lt_of_ne fun hc =>
        hne (Subgroup.eq_top_of_card_eq _ hc)

theorem not_l3u3Pumpup_of_card_le {S : Type} [Group S] [Finite S] (hF : L3U3Facts)
    (β : MulAut S) (hS : Nat.card S ≤ 20160) : ¬ L3U3Pumpup S β := by
  intro h
  obtain ⟨N, hN, -, hlt⟩ := h.exists_order_dvd_lt hF
  have := hN.ge_20160
  omega

theorem not_l3u3Pumpup_of_not_three_dvd {S : Type} [Group S] [Finite S] (hF : L3U3Facts)
    (β : MulAut S) (hS : ¬ 3 ∣ Nat.card S) : ¬ L3U3Pumpup S β := by
  intro h
  obtain ⟨N, hN, hdvd, -⟩ := h.exists_order_dvd_lt hF
  exact hS ((dvd_trans (by norm_num : 3 ∣ 9) hN.nine_dvd).trans hdvd)

theorem not_l3u3Pumpup_of_not_seven_dvd {S : Type} [Group S] [Finite S] (hF : L3U3Facts)
    (β : MulAut S) (h7 : ¬ 7 ∣ Nat.card S) (hS : Nat.card S ≤ 366157135872) :
    ¬ L3U3Pumpup S β := by
  intro h
  obtain ⟨N, hN, hdvd, hlt⟩ := h.exists_order_dvd_lt hF
  rcases hN.cases with ⟨-, h7N⟩ | hge
  · exact h7 (h7N.trans hdvd)
  · omega

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
