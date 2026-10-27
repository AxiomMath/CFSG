module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSpor
public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open Subgroup

theorem card_of_sporadic_M11
    {A : Type} [Group A] [Finite A] {L : Subgroup A}
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .M11).Group)) :
    Nat.card L = 7920 := by
  obtain ⟨e⟩ := e
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact ((Nat.card_congr e.toEquiv).trans (Nat.card_congr f.symm.toEquiv)).trans
    CFSG.Sporadic.Mathieu.card_M11

theorem pRank_three_le_two_of_card {A : Type} [Group A] [Finite A] {H L : Subgroup A}
    (hHL : H ≤ L) (hL : Nat.card L = 7920) : CFSG.Open.pRank 3 H ≤ 2 := by
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, hEH, -, hcard⟩
  by_contra hk
  have hdvd : Nat.card E ∣ Nat.card L := Subgroup.card_dvd_of_le (hEH.trans hHL)
  rw [hcard, hL] at hdvd
  have h27 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
  have h := h27.trans hdvd
  norm_num at h

theorem kFactSporM11_holds :
    KFactSporM11 := by
  intro A _ _ L hL U _ _ _
  have h := pRank_three_le_two_of_card (inf_le_right : normalizer (U : Set A) ⊓ L ≤ L)
    (card_of_sporadic_M11 hL)
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
