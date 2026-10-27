module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Lemma815
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian standardComponentIsStandard standardComponentOddCore ordTwistedA)
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding

section Orders

theorem three_dvd_card_of_psu_three {Q : Type} [Group Q] {m : ℕ}
    (h : StatedClassicalModel Q .PSU 3 2 m) : 3 ∣ Nat.card Q := by
  rw [EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical h]
  simp only [EvenSmallLie.CatalogOrders.lieOrd, ordTwistedA]
  rw [show (3 - 1 : ℕ) = 2 from rfl, show (2 + 1 : ℕ) = 3 from rfl,
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have ha : (((2 ^ m : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = (2 ^ m) ^ 2 - 1 := by
    have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (Nat.two_pow_pos m)
    rw [show ((2 ^ m : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2 = (((2 ^ m) ^ 2 - 1 : ℕ) : ℤ) by
      rw [Nat.cast_sub h1]; push_cast; ring]
    exact Int.toNat_natCast _
  have hb : (((2 ^ m : ℕ) : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = (2 ^ m) ^ 3 + 1 := by
    rw [show ((2 ^ m : ℕ) : ℤ) ^ 3 - (-1 : ℤ) ^ 3 = (((2 ^ m) ^ 3 + 1 : ℕ) : ℤ) by
      push_cast; ring]
    exact Int.toNat_natCast _
  rw [ha, hb]
  have h3a : 3 ∣ (2 ^ m) ^ 2 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow 4 1 m
    rw [one_pow, show (4 : ℕ) ^ m = (2 ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      at h
    exact h
  have hd : Nat.gcd 3 (2 ^ m + 1) ∣ 3 := Nat.gcd_dvd_left _ _
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · rw [h1, Nat.div_one]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h3a _) _
  · rw [h3]
    have hq3 : 3 ∣ 2 ^ m + 1 := h3 ▸ Nat.gcd_dvd_right 3 (2 ^ m + 1)
    have h3b : 3 ∣ (2 ^ m) ^ 3 + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow (2 ^ m) 1 (by decide : Odd 3)
      rw [one_pow] at this
      exact hq3.trans this
    apply Nat.dvd_div_of_mul_dvd
    exact Dvd.dvd.mul_left (Nat.mul_dvd_mul h3a h3b) _

theorem two_pow_seven_dvd_of_model {Q : Type} [Group Q] {t : StatedLieTag} {n m : ℕ}
    (hn : EvenSmallLie.CatalogOrders.lieMin t ≤ n)
    (he : 7 ≤ m * EvenSmallLie.CatalogOrders.lieExp t n) (h : StatedClassicalModel Q t n 2 m) :
    2 ^ 7 ∣ Nat.card Q := by
  rw [EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical h]
  refine dvd_trans ?_ (EvenSmallLie.CatalogOrders.pow_lieExp_dvd hn (2 ^ m))
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 he

end Orders

theorem false_of_psu_three (h2 : RankTwoBenderStandard)
    {H : Type} [Group H] [Finite H] {B : Subgroup H} (hB : RankTwoHyp H B)
    (hO : standardComponentOddCore H = ⊥) {m : ℕ} (hm : 2 ≤ m)
    (hT : StatedClassicalModel (rankTwoQuot B) .PSU 3 2 m) : False := by
  obtain ⟨hSz, -⟩ := h2 H B hB hO (Or.inr (Or.inl ⟨m, hm, hT⟩))
  exact RankTwoL3Even.not_three_dvd_card_of_suzukiModel_three hSz (three_dvd_card_of_psu_three hT)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Levi75.Y_ne_bot {A : Subgroup G} {D : ClassicalModel A} {T Y W L : Subgroup G}
    (hl : Levi75 D T Y W L) : Y ≠ ⊥ := by
  intro hY
  obtain ⟨F, _, _, -, ⟨e⟩⟩ := hl.W_type
  have hW : W ≤ ⊥ := hl.W_le.trans hY.le
  let x : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hx : x ≠ 1 := by
    intro h
    have h1 := congrArg
      (fun y : Matrix.SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [x] at h1
  apply hx
  have h1 : e.symm x = 1 := Subtype.ext (mem_bot.mp (hW (e.symm x).2))
  rw [← e.apply_symm_apply x, h1, map_one]

theorem classicalEvenType_of_model {Q : Type} [Group Q] {t : StatedLieTag} {n m : ℕ}
    (h : StatedClassicalModel Q t n 2 m)
    (ht : (t = .PSL ∧ 4 ≤ n) ∨ (t = .PSU ∧ 4 ≤ n) ∨ (t = .PSp ∧ 2 ≤ n) ∨
      ((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 4 ≤ n))
    (h7 : 2 ^ 7 ∣ Nat.card Q) : RankTwoClassicalEvenType Q := by
  refine ⟨?_, not_alternating_of_two_pow_seven_dvd h7⟩
  rcases ht with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl | rfl, hn⟩
  · exact Or.inl ⟨n, m, hn, h⟩
  · exact Or.inr (Or.inl ⟨n, m, hn, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, m, hn, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨n, m, hn, Or.inl h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨n, m, hn, Or.inr h⟩))

end CFSG.ComponentClassification.RankTwoClassical
