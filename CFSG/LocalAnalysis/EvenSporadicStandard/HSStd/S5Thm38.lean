module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem pRank_two_bot {G : Type*} [Group G] [Finite G] : Open.pRank 2 (⊥ : Subgroup G) = 0 := by
  unfold Open.pRank
  refine Nat.eq_zero_of_le_zero (csSup_le' ?_)
  rintro k ⟨E, hE, -, hcard⟩
  have hb : E = ⊥ := le_bot_iff.1 hE
  subst hb
  rw [Subgroup.card_bot] at hcard
  have : 2 ^ k = 1 := hcard.symm
  rcases Nat.pow_eq_one.1 this with h | h
  · omega
  · exact h.le

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.standardComponentOddCore_eq_bot {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hStd : StdHyp G L) :
    standardComponentOddCore G = ⊥ := by
  have hGeven : Even (Nat.card G) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 hStd.standard.2.1).trans
      (Subgroup.card_subgroup_dvd_card (centralizer (L : Set G))))
  unfold standardComponentOddCore
  refine le_antisymm (sSup_le ?_) bot_le
  rintro N ⟨hN, hodd⟩
  rcases hStd.simple.eq_bot_or_eq_top_of_normal N with hb | ht
  · exact hb ▸ le_rfl
  · exfalso
    subst ht
    rw [Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) hGeven

theorem hs_standard_rank_two_false
    (h38 : ComponentClassification.RankTwoSporadic.SporadicCaseOdd .HS) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hStd : StdHyp G L) {A' : Subgroup G}
    (hA' : standardComponentIsStandard A') (hq : IsSporadic (A' ⧸ center A') .HS)
    (hrk : 2 ≤ Open.pRank 2 (centralizer (A' : Set G))) : False := by
  have hnn : ¬ A'.Normal := by
    intro hN
    rcases hStd.simple.eq_bot_or_eq_top_of_normal A' with h | h
    · subst h
      have hs := hA'.1.2
      have : Nontrivial (↥(⊥ : Subgroup G) ⧸ center ↥(⊥ : Subgroup G)) := hs.toNontrivial
      have h2 : Nat.card (↥(⊥ : Subgroup G) ⧸ center ↥(⊥ : Subgroup G)) ∣
          Nat.card ↥(⊥ : Subgroup G) := Subgroup.card_quotient_dvd_card _
      rw [Subgroup.card_bot, Nat.dvd_one] at h2
      have h3 := Finite.one_lt_card (α := ↥(⊥ : Subgroup G) ⧸ center ↥(⊥ : Subgroup G))
      omega
    · subst h
      have hZ : center G = ⊥ := by
        rcases hStd.simple.eq_bot_or_eq_top_of_normal (center G) with hb | ht
        · exact hb
        · exfalso
          obtain ⟨a, b, hab⟩ := hStd.nonabelian
          have : a ∈ center G := ht ▸ Subgroup.mem_top a
          exact hab (Subgroup.mem_center_iff.1 this b).symm
      rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ, pRank_two_bot] at hrk
      omega
  exact h38 G A' ⟨hStd.kProper, hA', hnn, hrk⟩ hStd.standardComponentOddCore_eq_bot hq

end CFSG.EvenSporadicStandard.HSStd
