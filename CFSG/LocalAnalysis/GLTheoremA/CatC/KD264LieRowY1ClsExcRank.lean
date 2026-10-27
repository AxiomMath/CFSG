module

public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Yardstones.Md0ec50421ce4

theorem pRank_three_top_le_two_of_rankLE2 {K : Type} [Group K] [Finite K]
    (h : CFSG.LieType.SeitzGeneration.RankLE2 3 K) : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 := by
  refine csSup_le' ?_
  rintro k ⟨E, -, hE, hk⟩
  have h9 := h E hE
  rw [hk] at h9
  by_contra hc
  have h27 : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h9 h27
  omega

theorem pRank_three_top_le_zero_of_not_dvd {K : Type} [Group K] [Finite K] (h : ¬ 3 ∣ Nat.card K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 0 := by
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hk⟩
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · exact h0.le
  · exfalso
    apply h
    have hdvd : Nat.card E ∣ Nat.card K := Subgroup.card_subgroup_dvd_card E
    rw [hk] at hdvd
    exact (dvd_pow_self 3 hpos.ne').trans hdvd

theorem isChevSimple_three_of_char (d : TauCeti.ValidLieTypeIndex)
    (h : d.1.characteristic = 3) : IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group :=
  Or.inl ⟨TauCeti.CFSGIndex.lie d, h, ⟨MulEquiv.refl _⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
