module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem card_of_lieModel_psl_two {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2)
    (h : Blueprint.LieModel Y .PSL 2 p f) : Nat.card Y = Open.ordA 1 (p ^ f) :=
  (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).1 rfl

theorem card_of_lieModel_L34 {Y : Type} [Group Y] (h : Blueprint.LieModel Y .PSL 3 2 2) :
    Nat.card Y = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four (h.statedClassicalModel (by decide))

theorem eq_of_ordA_one_eq {m : ℕ} (h : Open.ordA 1 m = 60 ∨ Open.ordA 1 m = 168) :
    m = 4 ∨ m = 5 ∨ m = 7 := by
  have key : ∀ N : ℕ, N ≤ 2520 → Open.ordA 1 m = N → m < 18 := by
    intro N hN hm
    by_contra hge
    push Not at hge
    unfold Open.ordA at hm
    rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
      Finset.prod_singleton] at hm
    have hg : 0 < Nat.gcd 2 (m - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : Nat.gcd 2 (m - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hX : 2 * (2520 + 1) ≤ m * (m ^ 2 - 1) := by
      have h1 : 18 * 323 ≤ m * (m ^ 2 - 1) := by
        have h2 : 323 ≤ m ^ 2 - 1 := by
          have : 18 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hge 2
          omega
        exact Nat.mul_le_mul hge h2
      omega
    have h3 := lt_div_of_mul_succ_le hg hle hX
    have h4 : m * (m ^ 2 - 1) / Nat.gcd 2 (m - 1) = N := hm
    omega
  have hm18 : m < 18 := by
    rcases h with h | h
    · exact key 60 (by norm_num) h
    · exact key 168 (by norm_num) h
  unfold Open.ordA at h
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton] at h
  interval_cases m <;> simp_all

theorem ordA_one_ne_20160 (m : ℕ) : Open.ordA 1 m ≠ 20160 := by
  unfold Open.ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  rcases Nat.lt_or_ge m 35 with hm | hm
  · interval_cases m <;> decide
  · have hg : 0 < Nat.gcd 2 (m - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : Nat.gcd 2 (m - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hX : 2 * (20160 + 1) ≤ m * (m ^ 2 - 1) := by
      have h1 : 35 * 1224 ≤ m * (m ^ 2 - 1) := by
        have h2 : 1224 ≤ m ^ 2 - 1 := by
          have : 35 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
          omega
        exact Nat.mul_le_mul hm h2
      omega
    exact (lt_div_of_mul_succ_le hg hle hX).ne'

theorem pow_two_mul_ne_four_five_seven {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ (2 * f) ≠ 4 ∧ p ^ (2 * f) ≠ 5 ∧ p ^ (2 * f) ≠ 7 := by
  have hodd : Odd (p ^ (2 * f)) := (hp.odd_of_ne_two hp2).pow
  rw [pow_mul'] at hodd ⊢
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at hodd
    exact absurd hodd (by decide)
  all_goals
  · have hle : p ^ f ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have : 3 ^ 2 ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hlt 2
      omega
    interval_cases hpf : p ^ f <;> omega

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem row514_of (hB1 : ConjFixStatement) (hCF : CFProp23Fusion)
    (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 5 1 ∨ Blueprint.LieModel (OddBar h.J) .PSL 2 7 1)
    (hKa : conjugate h.K h.a = h.K) (hL : Blueprint.LieModel (ZStarBar h.K) .PSL 3 2 2) :
    h.Row514 := by
  have hcJ : Nat.card (OddBar h.J) = 60 ∨ Nat.card (OddBar h.J) = 168 := by
    rcases hJ with hJ | hJ
    · left; rw [card_of_lieModel_psl_two (by norm_num) hJ]; decide
    · right; rw [card_of_lieModel_psl_two (by norm_num) hJ]; decide
  have hJs : IsSimpleGroup (OddBar h.J) := by
    rcases hJ with hJ | hJ <;> exact isSimpleGroup_of_lieModel_psl_two hJ
  have hZJ : center (OddBar h.J) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_J
  have hcK : Nat.card (ZStarBar h.K) = 20160 := card_of_lieModel_L34 hL
  rcases h.table hB1 hCF with ⟨n, hn, ⟨eJ⟩, (⟨-, hK1 | hK1⟩ | ⟨hKa', -⟩)⟩ |
      h2 | ⟨hJ3, -⟩ | ⟨p, f, hp, hp2, hf, hJ4, -⟩ |
      ⟨p, f, hp, hp2, hf, -, -, -, hK5⟩ | ⟨-, -, -, -, -, -, -, hKa', -⟩ |
      ⟨p, f, hp, hp2, hf, hJ7, -⟩
  ·
    exfalso
    obtain ⟨eK⟩ := hK1
    have hZ : center (OddBar h.K) = ⊥ := center_eq_bot_of_mulEquiv_alternating (by omega) eK
    have hcK' : Nat.card (ZStarBar h.K) = (n + 2).factorial / 2 := by
      rw [card_zStarBar_of_center_eq_bot hZ, Nat.card_congr eK.toEquiv,
        nat_card_alternatingGroup, Nat.card_fin]
    rw [hcK] at hcK'
    have hcJn := Nat.card_congr eJ.toEquiv
    rcases hn with rfl | rfl | rfl <;>
    · rw [nat_card_alternatingGroup, Nat.card_fin] at hcJn
      rw [hcJn] at hcJ
      revert hcK' hcJ
      decide
  ·
    exfalso
    obtain ⟨eK⟩ := hK1
    have hZ : center (OddBar h.K) = ⊥ := center_eq_bot_of_mulEquiv_alternating (by omega) eK
    have hcK' : Nat.card (ZStarBar h.K) = (n + 4).factorial / 2 := by
      rw [card_zStarBar_of_center_eq_bot hZ, Nat.card_congr eK.toEquiv,
        nat_card_alternatingGroup, Nat.card_fin]
    rw [hcK] at hcK'
    have hcJn := Nat.card_congr eJ.toEquiv
    rcases hn with rfl | rfl | rfl <;>
    · rw [nat_card_alternatingGroup, Nat.card_fin] at hcJn
      rw [hcJn] at hcJ
      revert hcK' hcJ
      decide
  · exact absurd hKa hKa'
  · exact h2
  ·
    exfalso
    have := card_of_lieModel_L34 hJ3
    rw [card_zStarBar_of_center_eq_bot hZJ] at this
    omega
  ·
    exfalso
    rw [card_of_lieModel_psl_two hp2 hJ4] at hcJ
    obtain ⟨h4', h5', h7'⟩ := pow_two_mul_ne_four_five_seven (f := f) hp hp2
    rcases eq_of_ordA_one_eq hcJ with h4 | h5 | h7
    · exact h4' h4
    · exact h5' h5
    · exact h7' h7
  ·
    exfalso
    have hKs : IsSimpleGroup (OddBar h.K) := isSimpleGroup_of_lieModel_psl_two hK5
    have hZ : center (OddBar h.K) = ⊥ :=
      center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_K
    rw [card_zStarBar_of_center_eq_bot hZ, card_of_lieModel_psl_two hp2 hK5] at hcK
    exact ordA_one_ne_20160 _ hcK
  · exact absurd hKa hKa'
  ·
    exfalso
    rw [card_of_lieModel_psl_two hp2 hJ7] at hcJ
    obtain ⟨h4', h5', h7'⟩ := pow_two_mul_ne_four_five_seven (f := f) hp hp2
    rcases eq_of_ordA_one_eq hcJ with h4 | h5 | h7
    · exact h4' h4
    · exact h5' h5
    · exact h7' h7

theorem not_row514 (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexElim) (hST : SuzukiTausskyInput)
    (hP23 : CFProp23L34) (hRank : CFL34CoverRank) (hOut : CFL34CoverOut) (hAut : CFAutL2Rank)
    (hsec : h.SectionData) : ¬ h.Row514 := by
  intro hrow
  obtain ⟨hJ, hKa, hZK, hL⟩ := hrow
  have hT := h.card_T_quot_eq_two (hCFi H h (Or.inr (Or.inl ⟨hJ, hKa, hZK, hL⟩)))
  obtain ⟨H', _, _, h', ⟨eT⟩, ⟨eK⟩, -, -, hJ', hKa', -, -⟩ := hsec
  have hT' : Nat.card (↥h'.T ⧸ h'.B.subgroupOf h'.T) = 2 := (Nat.card_congr eT.toEquiv).trans hT
  have hJs : IsSimpleGroup (OddBar h.J) := by
    rcases hJ with hJ | hJ <;> exact isSimpleGroup_of_lieModel_psl_two hJ
  obtain ⟨eJ⟩ := hJ' (center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_J)
  have hJ'' : Blueprint.LieModel (OddBar h'.J) .PSL 2 5 1 ∨
      Blueprint.LieModel (OddBar h'.J) .PSL 2 7 1 := by
    rcases hJ with hJ | hJ
    · exact Or.inl (lieModel_of_mulEquiv_ne_zero eJ.symm (by norm_num) hJ)
    · exact Or.inr (lieModel_of_mulEquiv_ne_zero eJ.symm (by norm_num) hJ)
  have hL' : Blueprint.LieModel (ZStarBar h'.K) .PSL 3 2 2 :=
    lieModel_of_mulEquiv_ne_zero eK.symm (by norm_num) hL
  exact h'.false_of_row514 hB1 hB6 hB7 hCF23 hCF24 hCFc hST hP23 hRank hOut hAut hT'
    (h'.toHyp52.row514_of hB1 hCF23 hJ'' (hKa'.mpr hKa) hL')

end Hyp52

end CFSG.ComponentClassification.GSThmB
